#!/opt/homebrew/bin/fish
aiken build --trace-level verbose

aiken blueprint apply --validator "marlowe.execute" --out plutus.json 581c(cat plutus.json | jq -r '.validators[1].hash')

aiken blueprint convert --validator "marlowe.role_payout" > ../marlowe-plutus/marlowe-plutus/payout.plutus

aiken blueprint convert --validator "marlowe.execute" > ../marlowe-plutus/marlowe-plutus/semantics.plutus
