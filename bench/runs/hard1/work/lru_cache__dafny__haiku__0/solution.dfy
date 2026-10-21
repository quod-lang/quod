module Solution {
  function CountGets(ops: seq<(int, int, int)>, n: int): int
    requires 0 <= n <= |ops|
  {
    if n <= 0 then 0
    else
      var (kind, _, _) := ops[n-1];
      (if kind == 0 then 1 else 0) + CountGets(ops, n-1)
  }

  method lru_cache(capacity: int, ops: seq<(int, int, int)>) returns (out: seq<int>)
    requires capacity >= 1
    requires forall i :: 0 <= i < |ops| ==>
      var (kind, _, v) := ops[i];
      (kind == 0 || kind == 1) && (kind == 1 ==> v >= 0)
    ensures |out| == CountGets(ops, |ops|)
  {
    var cache: map<int, int> := map[];
    var order: seq<int> := [];
    out := [];
    var get_count := 0;

    for i := 0 to |ops|
      invariant |out| == get_count
      invariant get_count == CountGets(ops, i)
    {
      var (kind, key, value) := ops[i];

      if kind == 0 {
        if key in cache {
          out := out + [cache[key]];
          order := RemoveKeyAndAppend(order, key);
        } else {
          out := out + [-1];
        }
        get_count := get_count + 1;
      } else {
        if key in cache {
          cache := cache[key := value];
          order := RemoveKeyAndAppend(order, key);
        } else {
          if |order| > 0 {
            order := order[1..];
            cache := RemoveFromCache(cache, order);
          }
          cache := cache[key := value];
          order := order + [key];
        }
      }
    }
  }

  function RemoveKeyAndAppend(s: seq<int>, key: int): seq<int> {
    RemoveKey(s, key) + [key]
  }

  function RemoveKey(s: seq<int>, key: int): seq<int> {
    if |s| == 0 then []
    else if s[0] == key then RemoveKey(s[1..], key)
    else [s[0]] + RemoveKey(s[1..], key)
  }

  function RemoveFromCache(cache: map<int, int>, keys: seq<int>): map<int, int> {
    map k | k in keys && k in cache :: cache[k]
  }
}
