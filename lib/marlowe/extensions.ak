use aiken/dict.{to_list}
use aiken/list
use aiken/transaction/value.{Value, quantity_of, to_dict}

pub fn insert(self: List<(a, b)>, key: a, value: b) -> List<(a, b)> {
  when self is {
    [] ->
      [(key, value)]
    [(k, v), ..tail] ->
      if k == key {
        [(key, value), ..tail]
      } else {
        [(k, v), ..insert(tail, key, value)]
      }
  }
}

pub fn get(self: List<(a, b)>, key: a) -> Option<b> {
  when self is {
    [] -> None
    [(k, v), ..tail] ->
      if k == key {
        Some(v)
      } else {
        get(tail, key)
      }
  }
}

pub fn contains(self: List<(a, b)>, key: a) -> Bool {
  when self is {
    [] -> False
    [(k, _), ..tail] ->
      if k == key {
        True
      } else {
        contains(tail, key)
      }
  }
}

pub fn remove(self: List<(a, b)>, key: a) -> List<(a, b)> {
  when self is {
    [] ->
      []
    [(k, v), ..tail] ->
      if k == key {
        tail
      } else {
        [(k, v), ..remove(tail, key)]
      }
  }
}

pub fn greater_eq_value(self: Value, other: Value) -> Bool {
  other
    |> to_dict
    |> to_list
    |> list.all(
         fn(other_item) {
           let (other_policy, other_map) = other_item

           other_map
             |> to_list
             |> list.all(
                  fn(token) {
                    let (token_name, token_amount) = token

                    quantity_of(self, other_policy, token_name) >= token_amount
                  },
                )
         },
       )
}
