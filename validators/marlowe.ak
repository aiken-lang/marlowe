use aiken/builtin
use aiken/cbor
use aiken/dict
use aiken/interval.{Finite, Interval, IntervalBound}
use aiken/list
use aiken/math
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
use marlowe/extensions.{greater_eq_value}

type Datum {
  currency: PolicyId,
  role: AssetName,
}

validator {
  fn role_payout(datum: Datum, _red, ctx: ScriptContext) -> Bool {
    // clean way to pull out inputs from the script context
    let ScriptContext { transaction: Transaction { inputs, .. }, .. } = ctx

    let Datum { currency, role } = datum
    check_role_token_is_spent(inputs, currency, role)
  }
}

type MarloweParams {
  role_currency: ByteArray,
}

type Party {
  PAddress { network: Bool, address: Address }
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
  account_id: AccountId,
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

type Accounts =
  List<(IdToken, Int)>

type State {
  accounts: Accounts,
  choices: List<(ChoiceId, Int)>,
  bound_values: List<(ValueId, Int)>,
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
  start_time: Int,
  end_time: Int,
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

type ApplyAction {
  AppliedAction(ApplyWarning, State)
  NotAppliedAction
}

validator(validator_hash: ByteArray) {
  fn execute(
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
    let MarloweParams { role_currency: marlowe_params } = marlowe_params

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
            expect trace_if_false(output_reference == own_out_ref, @"x")
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
    expect
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
    expect check_state(@"i", script_in_value, marlowe_state)
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
            marlowe_params: MarloweParams { role_currency: marlowe_params },
            marlowe_state: state,
            marlowe_contract: contract,
          }

        let payouts_by_parties = list.foldr(payments, [], payout_by_party)

        // Each party must receive as least as much value as the semantics specify.
        // [Marlowe-Cardano Specification: "Constraint 15. Sufficient payment."]
        expect
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

                  trace_if_false(greater_eq_value(output_val, val), @"p")
                }
                PRole(role) -> {
                  let hsh =
                    dict.find(datums, Datum { currency: marlowe_params, role })

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
                          DatumHash(svh) -> and {
                              greater_eq_value(value, val)?,
                              (hsh == Some(svh))?,
                              (address == addr)?,
                            }
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
                  fail
                }
              }

            // [Marlowe-Cardano Specification: "Constraint 3. Single Marlowe output".]
            // [Marlowe-Cardano Specification: "Constraint 6. Output value to script."]
            // Check that the single Marlowe output has the correct datum and value.
            expect check_own_output(hsh, final_balance, own_output)
            // [Marlowe-Cardano Specification: "Constraint 18. Final balance."]
            // [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
            // [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
            // Check that the final state obeys the Semantic's invariants.
            expect check_state(@"o", final_balance, state)
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
            fail
          }
          TEApplyNoMatchError -> {
            trace @"n"
            fail
          }
          TEIntervalError(interval_error) ->
            when interval_error is {
              InvalidInterval(_) -> {
                trace @"j"
                fail
              }
              IntervalInPastError(_, _) -> {
                trace @"k"
                fail
              }
            }
          TEUselessTransaction -> {
            trace @"u"
            fail
          }
          TEHashMismatch -> {
            trace @"m"
            fail
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
  expect
    trace_if_false(
      list.foldr(
        accounts,
        value.zero(),
        fn(account, acc) {
          let (IdToken { token: Token { policy_id, asset_name }, .. }, balance) =
            account
          // [Marlowe-Cardano Specification: "Constraint 13. Positive balances".]
          expect trace_if_false(balance > 0, string.concat(@"b", tag))
          value.add(acc, policy_id, asset_name, balance)
        },
      ) == expected,
      string.concat(@"v", tag),
    )
  // [Marlowe-Cardano Specification: "Constraint 19. No duplicates".]
  expect trace_if_false(no_duplicates(accounts), string.concat(@"ea", tag))
  expect trace_if_false(no_duplicates(choices), string.concat(@"ec", tag))
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

    IntervalTrimmed(Environment { start_time: new_low, end_time: u }, new_low)
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
                list.concat(warnings, convert_apply_warning(apply_warn)),
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
    Close ->
      when refund_one(state.accounts) is {
        Some(((party, token, amount), new_accounts)) -> {
          let new_state = State { ..state, accounts: new_accounts }

          Reduced(
            ReduceNoWarning,
            ReduceWithPayment(Payment(party, Party(party), token, amount)),
            new_state,
            Close,
          )
        }
        None -> NotReduced
      }

    Pay(acc_id, payee, tok, val, cont) -> {
      let amount_to_pay = eval_value(env, state, val)

      if amount_to_pay <= 0 {
        let warning = ReduceNonPositivePay(acc_id, payee, tok, amount_to_pay)

        Reduced(warning, ReduceNoPayment, state, cont)
      } else {
        let balance = money_in_account(acc_id, tok, state.accounts)
        let paid_amount = math.min(balance, amount_to_pay)
        let new_balance = balance - paid_amount

        let new_accs =
          update_money_in_account(acc_id, tok, new_balance, state.accounts)

        let warning =
          if paid_amount < amount_to_pay {
            ReducePartialPay(acc_id, payee, tok, paid_amount, amount_to_pay)
          } else {
            ReduceNoWarning
          }

        let (payment, final_accs) =
          give_money(acc_id, payee, tok, paid_amount, new_accs)

        let new_state = State { ..state, accounts: final_accs }

        Reduced(warning, payment, new_state, cont)
      }
    }

    If(obs, cont1, cont2) -> {
      let cont =
        if eval_observation(env, state, obs) {
          cont1
        } else {
          cont2
        }

      Reduced(ReduceNoWarning, ReduceNoPayment, state, cont)
    }

    When(_, timeout, cont) -> {
      let Environment { start_time, end_time } = env

      // if timeout in future – do not reduce
      if end_time < timeout {
        NotReduced
      } else {
        // if timeout in the past – reduce to timeout continuation

        if timeout <= start_time {
          Reduced(ReduceNoWarning, ReduceNoPayment, state, cont)
        } else {
          // if timeout in the time range – issue an ambiguity error
          AmbiguousTimeIntervalReductionError
        }
      }
    }

    Let(val_id, val, cont) -> {
      let evaluated_value = eval_value(env, state, val)
      let bound_vals = state.bound_values
      // SCP-5126: Given the precondition that `boundValues` contains
      // no duplicate entries, this insertion behaves identically
      // (aside from internal ordering) to Marlowe's Isabelle semantics
      // given the precondition that the initial state's `boundValues`
      // in Isabelle was sorted and did not contain duplicate entries.
      let new_state =
        State {
          ..state,
          bound_values: extensions.insert(bound_vals, val_id, evaluated_value),
        }
      // SCP-5126: Given the precondition that `boundValues` contains
      // no duplicate entries, this lookup behaves identically to
      // Marlowe's Isabelle semantics given the precondition that the
      // initial state's `boundValues` in Isabelle was sorted and did
      // not contain duplicate entries.
      let warn =
        when extensions.get(bound_vals, val_id) is {
          Some(old_val) -> ReduceShadowing(val_id, old_val, evaluated_value)
          None -> ReduceNoWarning
        }

      Reduced(warn, ReduceNoPayment, new_state, cont)
    }

    Assert(obs, cont) -> {
      let warning =
        if eval_observation(env, state, obs) {
          ReduceNoWarning
        } else {
          ReduceAssertionFailed
        }

      Reduced(warning, ReduceNoPayment, state, cont)
    }
  }
}

fn eval_observation(env: Environment, state: State, obs: Observation) -> Bool {
  when obs is {
    AndObs(lhs, rhs) ->
      eval_observation(env, state, lhs) && eval_observation(env, state, rhs)
    OrObs(lhs, rhs) ->
      eval_observation(env, state, lhs) || eval_observation(env, state, rhs)
    NotObs(sub_obs) -> !eval_observation(env, state, sub_obs)
    // SCP-5126: Given the precondition that `choices` contains no
    // duplicate entries, this membership test behaves identically
    // to Marlowe's Isabelle semantics given the precondition that
    // the initial state's `choices` in Isabelle was sorted and did
    // not contain duplicate entries.
    ChoseSomething(choice_id) -> extensions.contains(state.choices, choice_id)
    ValueGE(lhs, rhs) ->
      eval_value(env, state, lhs) >= eval_value(env, state, rhs)
    ValueGT(lhs, rhs) ->
      eval_value(env, state, lhs) > eval_value(env, state, rhs)
    ValueLT(lhs, rhs) ->
      eval_value(env, state, lhs) < eval_value(env, state, rhs)
    ValueLE(lhs, rhs) ->
      eval_value(env, state, lhs) <= eval_value(env, state, rhs)
    ValueEQ(lhs, rhs) ->
      eval_value(env, state, lhs) == eval_value(env, state, rhs)
    TrueObs -> True
    FalseObs -> False
  }
}

fn eval_value(
  env: Environment,
  state: State,
  value_obs: Value<Observation>,
) -> Int {
  when value_obs is {
    AvailableMoney(acc_id, token) ->
      money_in_account(acc_id, token, state.accounts)
    Constant(integer) -> integer
    NegValue(val) -> 0 - eval_value(env, state, val)
    AddValue(lhs, rhs) ->
      eval_value(env, state, lhs) + eval_value(env, state, rhs)
    SubValue(lhs, rhs) ->
      eval_value(env, state, lhs) - eval_value(env, state, rhs)
    MulValue(lhs, rhs) ->
      eval_value(env, state, lhs) * eval_value(env, state, rhs)
    DivValue(lhs, rhs) -> {
      let n = eval_value(env, state, lhs)
      let d = eval_value(env, state, rhs)

      if d == 0 {
        0
      } else {
        builtin.quotient_integer(n, d)
      }
    }
    ChoiceValue(choice_id) ->
      // SCP-5126: Given the precondition that `choices` contains no
      // duplicate entries, this lookup behaves identically to
      // Marlowe's Isabelle semantics given the precondition that
      // the initial state's `choices` in Isabelle was sorted and
      // did not contain duplicate entries.
      when extensions.get(state.choices, choice_id) is {
        Some(choice) -> choice
        None -> 0
      }
    TimeIntervalStart -> {
      let Environment { start_time, .. } = env

      start_time
    }
    TimeIntervalEnd -> {
      let Environment { end_time, .. } = env

      end_time
    }
    UseValue(val_id) ->
      // SCP-5126: Given the precondition that `boundValues` contains
      // no duplicate entries, this lookup behaves identically to
      // Marlowe's Isabelle semantics given the precondition that
      // the initial state's `boundValues` in Isabelle was sorted
      // and did not contain duplicate entries.
      when extensions.get(state.bound_values, val_id) is {
        Some(val) -> val
        None -> 0
      }
    Cond(cond, thn, els) ->
      if eval_observation(env, state, cond) {
        eval_value(env, state, thn)
      } else {
        eval_value(env, state, els)
      }
  }
}

fn money_in_account(
  account_id: AccountId,
  token: Token,
  accounts: Accounts,
) -> Int {
  when extensions.get(accounts, IdToken { account_id, token }) is {
    Some(balance) -> balance
    None -> 0
  }
}

fn update_money_in_account(
  account_id: AccountId,
  token: Token,
  amount: Int,
  accounts: Accounts,
) -> Accounts {
  if amount <= 0 {
    extensions.remove(accounts, IdToken { account_id, token })
  } else {
    extensions.insert(accounts, IdToken { account_id, token }, amount)
  }
}

fn give_money(
  account_id: AccountId,
  payee: Payee,
  token: Token,
  amount: Int,
  accounts: Accounts,
) -> (ReduceEffect, Accounts) {
  let new_accounts =
    when payee is {
      Party(_) -> accounts
      Account(acc_id) -> add_money_to_account(acc_id, token, amount, accounts)
    }

  (ReduceWithPayment(Payment(account_id, payee, token, amount)), new_accounts)
}

fn add_money_to_account(
  acc_id: AccountId,
  token: Token,
  amount: Int,
  accounts: Accounts,
) -> Accounts {
  let balance = money_in_account(acc_id, token, accounts)

  let new_balance = balance + amount

  if amount <= 0 {
    accounts
  } else {
    update_money_in_account(acc_id, token, new_balance, accounts)
  }
}

fn refund_one(accounts: Accounts) -> Option<((Party, Token, Int), Accounts)> {
  when accounts is {
    [] -> None
    [(IdToken { account_id, token }, balance), ..rest] ->
      if balance > 0 {
        Some(((account_id, token, balance), rest))
      } else {
        refund_one(rest)
      }
  }
}

fn convert_reduce_warnings(
  warnings: List<ReduceWarning>,
) -> List<TransactionWarning> {
  list.foldr(
    warnings,
    [],
    fn(warning, acc) {
      when warning is {
        ReduceNoWarning -> acc
        ReduceNonPositivePay(acc_id, payee, tok, amount) ->
          [TransactionNonPositivePay(acc_id, payee, tok, amount), ..acc]
        ReducePartialPay(acc_id, payee, tok, paid, expected) ->
          [TransactionPartialPay(acc_id, payee, tok, paid, expected), ..acc]
        ReduceShadowing(val_id, old_val, new_val) ->
          [TransactionShadowing(val_id, old_val, new_val), ..acc]
        ReduceAssertionFailed ->
          [TransactionAssertionFailed, ..acc]
      }
    },
  )
}

fn convert_apply_warning(warning: ApplyWarning) -> List<TransactionWarning> {
  when warning is {
    ApplyNoWarning ->
      []
    ApplyNonPositiveDeposit(party, acc_id, tok, amount) ->
      [TransactionNonPositiveDeposit(party, acc_id, tok, amount)]
  }
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
  state: State,
  input: Input,
  cases: List<Case<Contract>>,
) -> ApplyResult {
  when cases is {
    [] -> ApplyNoMatchError
    [head_case, ..tail] -> {
      let input_content = get_input_content(input)
      let action = get_action(head_case)
      let opt_cont = get_continuation(input, head_case)

      when apply_action(env, state, input_content, action) is {
        AppliedAction(warning, new_state) ->
          when opt_cont is {
            Some(cont) -> Applied(warning, new_state, cont)
            None -> ApplyHashMismatch
          }
        NotAppliedAction -> apply_cases(env, state, input, tail)
      }
    }
  }
}

fn get_input_content(input: Input) -> InputContent {
  when input is {
    NormalInput(input_content) -> input_content
    MerkleizedInput(input_content, _, _) -> input_content
  }
}

fn get_action(case: Case<a>) -> Action {
  when case is {
    CCase(action, _) -> action
    CMerkleizedCase(action, _) -> action
  }
}

fn get_continuation(input: Input, case: Case<Contract>) -> Option<Contract> {
  when input is {
    NormalInput(_) ->
      when case is {
        CCase(_, cont) -> Some(cont)
        _ -> None
      }
    MerkleizedInput(_, input_cont_hash, cont) ->
      when case is {
        CMerkleizedCase(_, cont_hash) ->
          if input_cont_hash == cont_hash {
            Some(cont)
          } else {
            None
          }
        _ -> None
      }
  }
}

fn apply_action(
  env: Environment,
  state: State,
  input_content: InputContent,
  action: Action,
) -> ApplyAction {
  when input_content is {
    IDeposit(acc_id_1, party_1, tok_1, amount) ->
      when action is {
        Deposit(acc_id_2, party_2, tok_2, val) ->
          if
          acc_id_1 == acc_id_2 && party_1 == party_2 && tok_1 == tok_2 && amount == eval_value(
            env,
            state,
            val,
          ){
          
            let warning =
              if amount > 0 {
                ApplyNoWarning
              } else {
                ApplyNonPositiveDeposit(party_2, acc_id_2, tok_2, amount)
              }

            let new_accounts =
              add_money_to_account(acc_id_1, tok_1, amount, state.accounts)

            let new_state = State { ..state, accounts: new_accounts }

            AppliedAction(warning, new_state)
          } else {
            NotAppliedAction
          }
        _ -> NotAppliedAction
      }

    IChoice(choice_id_1, choice) ->
      when action is {
        Choice(choice_id_2, bounds) ->
          if choice_id_1 == choice_id_2 && in_bounds(bounds, choice) {
            // SCP-5126: Given the precondition that `choices` contains no
            // duplicate entries, this insertion behaves identically (aside
            // from internal ordering) to Marlowe's Isabelle semantics
            // given the precondition that the initial state's `choices`
            // in Isabelle was sorted and did not contain duplicate entries.
            let new_state =
              State {
                ..state,
                choices: extensions.insert(state.choices, choice_id_1, choice),
              }

            AppliedAction(ApplyNoWarning, new_state)
          } else {
            NotAppliedAction
          }
        _ -> NotAppliedAction
      }

    INotify ->
      when action is {
        Notify(obs) ->
          if eval_observation(env, state, obs) {
            AppliedAction(ApplyNoWarning, state)
          } else {
            NotAppliedAction
          }
        _ -> NotAppliedAction
      }
  }
}

fn in_bounds(self: List<Bound>, num: Int) -> Bool {
  list.any(
    self,
    fn(bound) {
      let Bound(l, u) = bound
      num >= l && num <= u
    },
  )
}
