use aiken/dict
use aiken/interval.{Finite, Interval, IntervalBound}
use aiken/list
use aiken/string
use aiken/transaction.{
  DatumHash, Input as ContextInput, Output, ScriptContext, Spend, Transaction,
}
use aiken/transaction/credential.{
  Address, ScriptCredential, VerificationKeyCredential,
}
use aiken/transaction/value.{
  AssetName, PolicyId, Value as ContextValue, quantity_of,
}

type Datum {
  currency: PolicyId,
  role: AssetName,
}

validator {
  fn role_payout_validator(datum: Datum, _red, ctx: ScriptContext) -> Bool {
    // clean way to pull out inputs from the script context
    let ScriptContext { transaction: Transaction { inputs, .. }, .. } = ctx

    let Datum { currency, role } = datum
    check_role_token_is_spent(inputs, currency, role)
  }
}

type MarloweParams =
  PolicyId

type Party {
  PAddress { network: Int, address: Address }
  PRole { asset_name: AssetName }
}

type AccountId =
  Party

type Token {
  policy_id: PolicyId,
  asset_name: AssetName,
}

type Payee {
  Account(AccountId)
  Party(Party)
}

type Payment {
  Payment(AccountId, Payee, Token, Int)
}

type IdToken {
  account_id: Party,
  token: Token,
}

type ChoiceId {
  choice_name: ByteArray,
  party: Party,
}

type ValueId {
  id: ByteArray,
}

type TimeOut =
  Int

type Bound {
  Bound(Int, Int)
}

type Value<a> {

  AvailableMoney(AccountId, Token)
  Constant(Int)
  NegValue(Value<a>)
  AddValue(Value<a>, Value<a>)
  SubValue(Value<a>, Value<a>)
  MulValue(Value<a>, Value<a>)
  DivValue(Value<a>, Value<a>)
  ChoiceValue(ChoiceId)
  TimeIntervalStart
  TimeIntervalEnd
  UseValue(ValueId)
  Cond(a, Value<a>, Value<a>)
}

type Observation {
  AndObs(Observation, Observation)
  OrObs(Observation, Observation)
  NotObs(Observation)
  ChoseSomething(ChoiceId)
  ValueGE(Value<Observation>, Value<Observation>)
  ValueGT(Value<Observation>, Value<Observation>)
  ValueLT(Value<Observation>, Value<Observation>)
  ValueLE(Value<Observation>, Value<Observation>)
  ValueEQ(Value<Observation>, Value<Observation>)
  TrueObs
  FalseObs
}

type Action {
  Deposit {
    account: AccountId,
    party: Party,
    token: Token,
    obs_val: Value<Observation>,
  }
  Choice(ChoiceId, List<Bound>)
  Notify(Observation)
}

type State {
  accounts: List<(IdToken, Int)>,
  choices: List<(ChoiceId, Int)>,
  bound_values: List<(ByteArray, Int)>,
  min_time: Int,
}

type Case<a> {
  CCase(Action, a)
  CMerkleizedCase(Action, ByteArray)
}

type Contract {
  Close
  Pay(Party, Payee, Token, Value<Observation>, Contract)
  If(Observation, Contract, Contract)
  When(List<Case<Contract>>, TimeOut, Contract)
  Let(ValueId, Value<Observation>, Contract)
  Assert(Observation, Contract)
}

type MarloweData {
  marlowe_params: MarloweParams,
  marlowe_state: State,
  marlowe_contract: Contract,
}

type Input {
  NormalInput(InputContent)
  MerkleizedInput(InputContent, ByteArray, Contract)
}

type TransactionInput {
  tx_interval: (Int, Int),
  tx_inputs: List<Input>,
}

type TransactionWarning {
  TransactionNonPositiveDeposit(Party, AccountId, Token, Int)
  TransactionNonPositivePay(AccountId, Payee, Token, Int)
  TransactionPartialPay(AccountId, Payee, Token, Int, Int)
  //                       ^ src    ^ dest       ^ paid ^ expected
  TransactionShadowing(ValueId, Int, Int)
  //                      oldVal ^    ^ newVal 
  TransactionAssertionFailed
}

type ReduceWarning {
  ReduceNoWarning
  ReduceNonPositivePay(AccountId, Payee, Token, Int)
  ReducePartialPay(AccountId, Payee, Token, Int, Int)
  ReduceShadowing(ValueId, Int, Int)
  ReduceAssertionFailed
}

type ReduceResult {
  ContractQuiescent(Bool, List<ReduceWarning>, List<Payment>, State, Contract)
  RRAmbiguousTimeIntervalError
}

type ReduceStepResult {
  Reduced(ReduceWarning, ReduceEffect, State, Contract)
  NotReduced
  AmbiguousTimeIntervalReductionError
}

type ReduceEffect {
  ReduceWithPayment(Payment)
  ReduceNoPayment
}

type TransactionError {
  TEAmbiguousTimeIntervalError
  TEApplyNoMatchError
  TEIntervalError(IntervalErrorType)
  TEUselessTransaction
  TEHashMismatch
}

type TransactionOutput {
  TransactionOutput {
    warnings: List<TransactionWarning>,
    payments: List<Payment>,
    state: State,
    contract: Contract,
  }

  Error(TransactionError)
}

type MarloweInput =
  List<MarloweTxInput>

type InputContent {
  IDeposit(AccountId, Party, Token, Int)
  IChoice(ChoiceId, Int)
  INotify
}

type MarloweTxInput {
  TxInput(InputContent)
  MerkleizedTxInput(InputContent, ByteArray)
}

type IntervalErrorType {
  InvalidInterval((Int, Int))
  IntervalInPastError(Int, (Int, Int))
}

type IntervalResult {
  IntervalTrimmed(Environment, Int)
  IntervalError(IntervalErrorType)
}

type Environment {
  time_interval: (Int, Int),
}

type ApplyWarning {
  ApplyNoWarning
  ApplyNonPositiveDeposit(Party, AccountId, Token, Int)
}

type ApplyResult {
  Applied(ApplyWarning, State, Contract)
  ApplyNoMatchError
  ApplyHashMismatch
}

type ApplyAllResult {
  ApplyAllSuccess(
    Bool,
    List<TransactionWarning>,
    List<Payment>,
    State,
    Contract,
  )
  ApplyAllNoMatchError
  ApplyAllAmbiguousTimeIntervalError
  ApplyAllHashMismatch
}

const ada_policy = ""

validator(validator_hash: ByteArray) {
  fn marlowe_validator(
    datum: MarloweData,
    redeemer: MarloweInput,
    ctx: ScriptContext,
  ) -> Bool {
    let ScriptContext { transaction, purpose } = ctx
    expect Spend(own_out_ref) = purpose

    let Transaction {
      inputs: tx_inputs,
      outputs: tx_outputs,
      validity_range: Interval { lower_bound, upper_bound },
      datums,
      extra_signatories,
      ..
    } = transaction

    let MarloweData { marlowe_params, marlowe_state, marlowe_contract } = datum

    expect Some(own_input) =
      list.find(tx_inputs, fn(input) { input.output_reference == own_out_ref })

    let ContextInput {
      output: Output { value: script_in_value, address: own_address, .. },
      ..
    } = own_input

    // [Marlowe-Cardano Specification: "2. Single Marlowe script input".]
    // The inputs being spent by this script, and whether other validators are present.
    let other_validators =
      list.any(
        tx_inputs,
        fn(input) {
          let ContextInput { output_reference, output } = input
          let Output { address: addr, .. } = output

          // TODO: maybe check on payment cred equality instead of full address
          if addr == own_address {
            expect True = trace_if_false(output_reference == own_out_ref, @"x")

            False
          } else {
            when addr.payment_credential is {
              ScriptCredential(_) -> True
              _ -> False
            }
          }
        },
      )

    let interval = close_interval(lower_bound, upper_bound)

    let inputs =
      list.map(
        redeemer,
        fn(input: MarloweTxInput) -> Input {
          when input is {
            MerkleizedTxInput(input, hash) -> {
              expect Some(datum) = dict.get(datums, hash)

              expect contract: Contract = datum
              MerkleizedInput(input, hash, contract)
            }
            TxInput(input) -> NormalInput(input)
          }
        },
      )

    let input_contents =
      list.map(
        inputs,
        fn(input: Input) {
          when input is {
            NormalInput(content) -> content
            MerkleizedInput(content, _, _) -> content
          }
        },
      )

    // Validate all inputs are authorized
    // Check that the required signatures and role tokens are present.
    // [Marlowe-Cardano Specification: "Constraint 14. Inputs authorized".]
    expect True =
      list.all(
        input_contents,
        fn(input_content) {
          let validate_witness_party =
            fn(party) -> Bool {
              when party is {
                PAddress(_, Address { payment_credential, .. }) -> {
                  expect VerificationKeyCredential(pkh) = payment_credential
                  list.has(extra_signatories, pkh)
                }
                PRole(role) ->
                  check_role_token_is_spent(tx_inputs, marlowe_params, role)
              }
            }

          when input_content is {
            // The party must witness a deposit.
            IDeposit(_, party, _, _) -> validate_witness_party(party)
            // The party must witness a choice.
            IChoice(ChoiceId { party, .. }, _) -> validate_witness_party(party)
            // No witness is needed for a notify.
            INotify -> True
          }
        },
      )

    // [Marlowe-Cardano Specification: "Constraint 5. Input value from script".]
    // [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
    // [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
    // Check that the initial state obeys the Semantic's invariants.
    expect True = check_state(@"i", script_in_value, marlowe_state)

    // [Marlowe-Cardano Specification: "Constraint 0. Input to semantics".]
    // Package the inputs to be applied in the semantics.
    let tx_input = TransactionInput { tx_interval: interval, tx_inputs: inputs }

    // [Marlowe-Cardano Specification: "Constraint 7. Input state".]
    // [Marlowe-Cardano Specification: "Constraint 8. Input contract".]
    // The semantics computation operates on the state and contract from
    // the incoming datum.
    let computed_result =
      compute_transaction(tx_input, marlowe_state, marlowe_contract)

    when computed_result is {
      TransactionOutput { payments, state, contract, .. } -> {
        // [Marlowe-Cardano Specification: "Constraint 9. Marlowe parameters".]
        // [Marlowe-Cardano Specification: "Constraint 10. Output state".]
        // [Marlowe-Cardano Specification: "Constraint 11. Output contract."]
        // The output datum maintains the parameters and uses the state
        // and contract resulting from the semantics computation.
        let marlowe_data =
          MarloweData {
            marlowe_params,
            marlowe_state: state,
            marlowe_contract: contract,
          }

        let payouts_by_parties = list.foldr(payments, [], payout_by_party)

        // Each party must receive as least as much value as the semantics specify.
        // [Marlowe-Cardano Specification: "Constraint 15. Sufficient payment."]
        expect True =
          list.all(
            payouts_by_parties,
            fn(payout) -> Bool {
              let (party, val) = payout

              when party is {
                PAddress(_, address) -> {
                  let output_val =
                    list.foldr(
                      tx_outputs,
                      value.zero(),
                      fn(output, acc) {
                        if output.address == address {
                          value.merge(output.value, acc)
                        } else {
                          acc
                        }
                      },
                    )

                  // None of these should fail unless ada is missing 
                  expect [(p_ada_policy, p_ada_balance), ..p_rest_values] =
                    dict.to_list(value.to_dict(val))

                  expect [(_, p_ada_amount)] = dict.to_list(p_ada_balance)

                  expect [(o_ada_policy, o_ada_balance), ..o_rest_values] =
                    dict.to_list(value.to_dict(output_val))

                  expect [(_, o_ada_amount)] = dict.to_list(o_ada_balance)

                  expect True =
                    trace_if_false(
                      o_ada_amount >= p_ada_amount && p_ada_policy == ada_policy && o_ada_policy == ada_policy,
                      @"p",
                    )

                  trace_if_false(p_rest_values == o_rest_values, @"p")
                }

                PRole(role) -> {
                  let hsh = dict.find(datums, (marlowe_params, role))

                  let addr =
                    Address {
                      payment_credential: ScriptCredential(validator_hash),
                      stake_credential: None,
                    }

                  trace_if_false(
                    list.any(
                      tx_outputs,
                      fn(output) {
                        let Output { address, value, datum, .. } = output

                        when datum is {
                          DatumHash(svh) ->
                            val == value && hsh == Some(svh) && address == addr
                          _ -> False
                        }
                      },
                    ),
                    @"r",
                  )
                }
              }
            },
          )

        when contract is {
          // [Marlowe-Cardano Specification: "Constraint 4. No output to script on close".]
          Close ->
            trace_if_false(
              !list.any(
                tx_outputs,
                fn(output) { output.address == own_address },
              ),
              @"c",
            )

          _ -> {
            let total_income =
              list.foldr(
                input_contents,
                value.zero(),
                fn(input, acc) {
                  when input is {
                    IDeposit(_, _, Token { policy_id, asset_name }, balance) ->
                      if balance > 0 {
                        value.add(acc, policy_id, asset_name, balance)
                      } else {
                        acc
                      }
                    _ -> acc
                  }
                },
              )

            let total_payouts =
              list.foldr(
                payouts_by_parties,
                value.zero(),
                fn(payout, acc) {
                  let (_, val) = payout

                  value.merge(acc, val)
                },
              )

            let final_balance =
              value.merge(
                value.merge(script_in_value, total_income),
                value.negate(total_payouts),
              )

            let hsh = dict.find(datums, marlowe_data)

            let own_output =
              when
                list.filter(
                  tx_outputs,
                  fn(output) { output.address == own_address },
                )
              is {
                [output] -> output
                _ -> {
                  trace @"o"
                  error
                }
              }

            // [Marlowe-Cardano Specification: "Constraint 3. Single Marlowe output".]
            // [Marlowe-Cardano Specification: "Constraint 6. Output value to script."]
            // Check that the single Marlowe output has the correct datum and value.
            expect True = check_own_output(hsh, final_balance, own_output)

            // [Marlowe-Cardano Specification: "Constraint 18. Final balance."]
            // [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
            // [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
            // Check that the final state obeys the Semantic's invariants.
            expect True = check_state(@"o", final_balance, state)

            // [Marlowe-Cardano Specification: "20. Single satsifaction".]
            // Either there must be no payouts, or there must be no other validators.
            trace_if_false(
              when payouts_by_parties is {
                [] -> True
                _ -> !other_validators
              },
              @"z",
            )
          }
        }
      }

      Error(e) ->
        when e is {
          TEAmbiguousTimeIntervalError -> {
            trace @"i"
            error
          }
          TEApplyNoMatchError -> {
            trace @"n"
            error
          }
          TEIntervalError(interval_error) ->
            when interval_error is {
              InvalidInterval(_) -> {
                trace @"j"
                error
              }
              IntervalInPastError(_, _) -> {
                trace @"k"
                error
              }
            }
          TEUselessTransaction -> {
            trace @"u"
            error
          }
          TEHashMismatch -> {
            trace @"m"
            error
          }
        }
    }
  }
}

fn check_role_token_is_spent(
  inputs: List<ContextInput>,
  policy: PolicyId,
  token_name: AssetName,
) -> Bool {
  when inputs is {
    [] -> False
    [input, ..rest_inputs] -> {
      let ContextInput { output: Output { value, .. }, .. } = input

      if quantity_of(value, policy, token_name) == 0 {
        check_role_token_is_spent(rest_inputs, policy, token_name)
      } else {
        True
      }
    }
  }
}

fn close_interval(
  lower_bound: IntervalBound<Int>,
  upper_bound: IntervalBound<Int>,
) -> (Int, Int) {
  let IntervalBound { bound_type: l_bound_type, is_inclusive: l_is_inclusive } =
    lower_bound
  let IntervalBound { bound_type: u_bound_type, is_inclusive: u_is_inclusive } =
    upper_bound

  expect Finite(l) = l_bound_type
  expect Finite(u) = u_bound_type

  let ci =
    (
      l + 1 - if l_is_inclusive {
        1
      } else {
        0
      },
      u - 1 + if u_is_inclusive {
        1
      } else {
        0
      },
    )
  ci
}

fn check_state(tag: String, expected: ContextValue, state: State) -> Bool {
  let State { accounts, choices, bound_values, .. } = state

  // [Marlowe-Cardano Specification: "Constraint 5. Input value from script".]
  // and/or
  // [Marlowe-Cardano Specification: "Constraint 18. Final balance."]
  expect True =
    trace_if_false(
      list.foldr(
        accounts,
        value.zero(),
        fn(account, acc) {
          let (IdToken { token: Token { policy_id, asset_name }, .. }, balance) =
            account

          // [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
          expect True = trace_if_false(balance > 0, string.concat(@"b", tag))

          value.add(acc, policy_id, asset_name, balance)
        },
      ) == expected,
      string.concat(@"v", tag),
    )

  // [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
  expect True =
    trace_if_false(no_duplicates(accounts), string.concat(@"ea", tag))

  expect True =
    trace_if_false(no_duplicates(choices), string.concat(@"ec", tag))

  trace_if_false(no_duplicates(bound_values), string.concat(@"eb", tag))
}

fn trace_if_false(expression: Bool, msg: String) -> Bool {
  if expression {
    True
  } else {
    trace msg
    False
  }
}

fn no_duplicates(xs: List<a>) -> Bool {
  when xs is {
    [] -> True
    [x, ..xs] ->
      if list.has(xs, x) {
        False
      } else {
        no_duplicates(xs)
      }
  }
}

fn payout_by_party(
  payment: Payment,
  acc: List<(Party, ContextValue)>,
) -> List<(Party, ContextValue)> {
  let Payment(_, payee, Token { policy_id, asset_name }, amount) = payment

  when payee is {
    Party(party) ->
      if amount > 0 {
        [(party, value.from_asset(policy_id, asset_name, amount)), ..acc]
      } else {
        acc
      }
    Account(_) -> acc
  }
}

fn compute_transaction(
  input: TransactionInput,
  state: State,
  contract: Contract,
) -> TransactionOutput {
  let TransactionInput { tx_inputs, tx_interval } = input
  let State { min_time, .. } = state

  when fix_interval(tx_interval, min_time) is {
    IntervalTrimmed(env, new_min_time) ->
      when
        apply_all_inputs(
          env,
          State { ..state, min_time: new_min_time },
          contract,
          tx_inputs,
        )
      is {
        ApplyAllSuccess(reduced, warnings, payments, new_state, cont) ->
          if reduced || Close == contract && !list.is_empty(state.accounts) {
            TransactionOutput {
              warnings,
              payments,
              state: new_state,
              contract: cont,
            }
          } else {
            Error(TEUselessTransaction)
          }
        ApplyAllNoMatchError -> Error(TEApplyNoMatchError)
        ApplyAllAmbiguousTimeIntervalError ->
          Error(TEAmbiguousTimeIntervalError)
        ApplyAllHashMismatch -> Error(TEHashMismatch)
      }
    IntervalError(m_error) -> Error(TEIntervalError(m_error))
  }
}

fn fix_interval(interval: (Int, Int), min_time: Int) -> IntervalResult {
  let (l, u) = interval

  if u < l {
    IntervalError(InvalidInterval(interval))
  } else if u < min_time {
    IntervalError(IntervalInPastError(min_time, interval))
  } else {
    let curr_min_time = min_time
    let new_low =
      if l < curr_min_time {
        curr_min_time
      } else {
        l
      }

    IntervalTrimmed(Environment { time_interval: (new_low, u) }, new_low)
  }
}

fn check_own_output(
  data: Option<ByteArray>,
  val: ContextValue,
  output: Output,
) -> Bool {
  let Output { value, datum, .. } = output

  trace_if_false(
    when datum is {
      DatumHash(svh) -> value == val && data == Some(svh)
      _ -> False
    },
    @"d",
  )
}

fn apply_all_inputs(
  env: Environment,
  state: State,
  contract: Contract,
  inputs: List<Input>,
) -> ApplyAllResult {
  //marlowe vm stuff
  apply_all_loop(False, env, state, contract, inputs, [], [])
}

fn apply_all_loop(
  contract_changed: Bool,
  env: Environment,
  state: State,
  contract: Contract,
  inputs: List<Input>,
  warnings: List<TransactionWarning>,
  payments: List<Payment>,
) {
  when reduce_contract_until_quiescent(env, state, contract) is {
    RRAmbiguousTimeIntervalError -> ApplyAllAmbiguousTimeIntervalError
    ContractQuiescent(reduced, reduce_warnings, pays, current_state, cont) -> {
      let warnings =
        list.concat(warnings, convert_reduce_warnings(reduce_warnings))

      let payments = list.concat(payments, pays)

      when inputs is {
        [] ->
          ApplyAllSuccess(
            contract_changed || reduced,
            warnings,
            payments,
            current_state,
            cont,
          )

        [input, ..rest] ->
          when apply_input(env, current_state, input, cont) is {
            Applied(apply_warn, new_state, next_cont) ->
              apply_all_loop(
                True,
                env,
                new_state,
                next_cont,
                rest,
                list.concat(warnings, convert_apply_warnings(apply_warn)),
                payments,
              )
            ApplyNoMatchError -> ApplyAllNoMatchError
            ApplyHashMismatch -> ApplyAllHashMismatch
          }
      }
    }
  }
}

/// Reduce a contract until it cannot be reduced more.
fn reduce_contract_until_quiescent(
  env: Environment,
  state: State,
  contract: Contract,
) -> ReduceResult {
  reduction_loop(False, env, state, contract, [], [])
}

fn reduction_loop(
  reduced: Bool,
  env: Environment,
  state: State,
  contract: Contract,
  warnings: List<ReduceWarning>,
  payments: List<Payment>,
) -> ReduceResult {
  when reduce_contract_step(env, state, contract) is {
    Reduced(warning, effect, new_state, cont) -> {
      let new_warnings =
        when warning is {
          ReduceNoWarning -> warnings
          _ ->
            [warning, ..warnings]
        }

      let new_payments =
        when effect is {
          ReduceWithPayment(payment) ->
            [payment, ..payments]
          ReduceNoPayment -> payments
        }

      reduction_loop(True, env, new_state, cont, new_warnings, new_payments)
    }

    AmbiguousTimeIntervalReductionError -> RRAmbiguousTimeIntervalError

    // this is the last invocation of reductionLoop, so we can reverse lists
    NotReduced ->
      ContractQuiescent(
        reduced,
        list.reverse(warnings),
        list.reverse(payments),
        state,
        contract,
      )
  }
}

/// Carry a step of the contract with no inputs.
fn reduce_contract_step(env: Environment, state: State, contract: Contract) {
  when contract is {
    // SCP-5126: Although `refundOne` refunds accounts-token combinations
    // in least-recently-added order and Isabelle semantics requires that
    // they be refunded in lexicographic order, `reduceContractUntilQuiescent`
    // ensures that the `Close` pattern will be executed until `accounts`
    // is empty. Thus, the net difference between the behavior here and the
    // Isabelle semantics is that the `ContractQuiescent` resulting from
    // `reduceContractUntilQuiescent` will contain payments in a different
    // order.
    Close -> todo
    Pay(acc_id, payee, tok, val, cont) -> todo
    If(obs, cont1, cont2) -> todo
    When(_, timeout, cont) -> todo
    Let(val_id, val, cont) -> todo
    Assert(obs, cont) -> todo
  }
}

fn convert_reduce_warnings(
  warnings: List<ReduceWarning>,
) -> List<TransactionWarning> {
  todo
}

fn convert_apply_warnings(warnings: ApplyWarning) -> List<TransactionWarning> {
  todo
}

fn apply_input(
  env: Environment,
  current_state: State,
  input: Input,
  cont: Contract,
) -> ApplyResult {
  when cont is {
    When(cases, _, _) -> apply_cases(env, current_state, input, cases)
    _ -> ApplyNoMatchError
  }
}

fn apply_cases(
  env: Environment,
  current_state: State,
  input: Input,
  cases: List<Case<Contract>>,
) -> ApplyResult {
  todo
}
