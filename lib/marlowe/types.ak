use aiken/transaction/credential.{Address}
use aiken/transaction/value.{AssetName, PolicyId}

pub type Datum {
  currency: PolicyId,
  role: AssetName,
}

pub type MarloweParams {
  role_currency: ByteArray,
}

pub type Party {
  PartyAddress { network: Bool, address: Address }
  Role { asset_name: AssetName }
}

pub type AccountId =
  Party

pub type Token {
  policy_id: PolicyId,
  asset_name: AssetName,
}

pub type Payee {
  AccountPayee(AccountId)
  PartyPayee(Party)
}
