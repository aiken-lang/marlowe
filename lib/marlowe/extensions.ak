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
