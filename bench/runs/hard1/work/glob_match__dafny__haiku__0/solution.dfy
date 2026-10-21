module Solution {
  predicate matches(pattern: string, text: string, p: int, t: int)
    requires 0 <= p <= |pattern|
    requires 0 <= t <= |text|
    decreases |pattern| - p, |text| - t
  {
    if p == |pattern| then
      t == |text|
    else if pattern[p] == '\\' && p + 1 < |pattern| then
      // Escaped character - must match the next char literally
      t < |text| && pattern[p + 1] == text[t] && matches(pattern, text, p + 2, t + 1)
    else if pattern[p] == '\\' && p + 1 == |pattern| then
      // Lone backslash at end matches literal backslash
      t < |text| && text[t] == '\\' && t + 1 == |text|
    else if pattern[p] == '*' then
      // Star matches 0 or more characters
      (exists i {:trigger matches(pattern, text, p + 1, i)} :: t <= i <= |text| && matches(pattern, text, p + 1, i))
    else if pattern[p] == '?' then
      // Question mark matches exactly one character
      t < |text| && matches(pattern, text, p + 1, t + 1)
    else
      // Regular character matches itself
      t < |text| && pattern[p] == text[t] && matches(pattern, text, p + 1, t + 1)
  }

  method glob_match(pattern: string, text: string) returns (b: bool)
    ensures b == matches(pattern, text, 0, 0)
  {
    b := matchesHelper(pattern, text, 0, 0);
  }

  method matchesHelper(pattern: string, text: string, p: int, t: int) returns (b: bool)
    requires 0 <= p <= |pattern|
    requires 0 <= t <= |text|
    ensures b == matches(pattern, text, p, t)
    decreases |pattern| - p, |text| - t
  {
    if p == |pattern| {
      b := t == |text|;
    } else if pattern[p] == '\\' && p + 1 < |pattern| {
      if t < |text| && pattern[p + 1] == text[t] {
        b := matchesHelper(pattern, text, p + 2, t + 1);
      } else {
        b := false;
      }
    } else if pattern[p] == '\\' && p + 1 == |pattern| {
      b := t < |text| && text[t] == '\\' && t + 1 == |text|;
    } else if pattern[p] == '*' {
      // For star, try matching 0 or more characters with the following pattern
      b := false;
      var i := t;
      while i <= |text|
        invariant t <= i && i <= |text| + 1
        invariant b ==> (exists j {:trigger matches(pattern, text, p + 1, j)} :: t <= j < i && matches(pattern, text, p + 1, j))
        invariant (exists j {:trigger matches(pattern, text, p + 1, j)} :: t <= j < i && matches(pattern, text, p + 1, j)) ==> b
        decreases |text| - i
      {
        var m := matchesHelper(pattern, text, p + 1, i);
        if m {
          b := true;
        }
        i := i + 1;
      }
    } else if pattern[p] == '?' {
      if t < |text| {
        b := matchesHelper(pattern, text, p + 1, t + 1);
      } else {
        b := false;
      }
    } else {
      if t < |text| && pattern[p] == text[t] {
        b := matchesHelper(pattern, text, p + 1, t + 1);
      } else {
        b := false;
      }
    }
  }
}
