module Solution {
  method topo_sort(n: int, edges: seq<(int, int)>) returns (result: seq<int>)
    requires n >= 1
    requires forall i :: 0 <= i < |edges| ==>
      0 <= edges[i].0 < n && 0 <= edges[i].1 < n
    ensures |result| == 0 || |result| == n
  {
    var has_self_loop := false;
    var i := 0;
    while i < |edges|
      invariant 0 <= i <= |edges|
    {
      if edges[i].0 == edges[i].1 {
        has_self_loop := true;
      }
      i := i + 1;
    }

    if has_self_loop {
      return [];
    }

    var in_degree := seq(n, node => CountInDegreeHelper(edges, node, 0));
    var order: seq<int> := [];
    var processed := seq(n, _ => false);

    var step := 0;
    while step < n
      invariant step == |order|
      invariant |processed| == n
      invariant |in_degree| == n
      decreases n - step
    {
      var chosen := FindMinUnprocessedWithZeroInDegree(n, processed, in_degree);

      if chosen == -1 {
        return [];
      }

      assert 0 <= chosen < n;
      order := order + [chosen];
      processed := UpdateProcessed(n, processed, chosen);
      in_degree := UpdateInDegrees(n, in_degree, edges, chosen);

      step := step + 1;
    }

    if step != n {
      return [];
    }
    return order;
  }

  function UpdateProcessed(n: int, processed: seq<bool>, chosen: int): seq<bool>
    requires |processed| == n
    requires 0 <= chosen < n
    ensures |UpdateProcessed(n, processed, chosen)| == n
  {
    seq(n, j => if 0 <= j < n && j == chosen then true else (if 0 <= j < n then processed[j] else false))
  }

  function UpdateInDegrees(n: int, in_degree: seq<int>, edges: seq<(int, int)>, chosen: int): seq<int>
    requires |in_degree| == n
    requires forall i :: 0 <= i < |edges| ==>
      0 <= edges[i].0 < n && 0 <= edges[i].1 < n
    requires 0 <= chosen < n
    ensures |UpdateInDegrees(n, in_degree, edges, chosen)| == n
  {
    seq(n, k => if 0 <= k < n then UpdateInDegreeHelper(in_degree, edges, k, chosen, 0) else 0)
  }

  function CountInDegreeHelper(edges: seq<(int, int)>, node: int, idx: int): int
    requires 0 <= idx <= |edges|
    decreases |edges| - idx
  {
    if idx == |edges| then 0
    else if edges[idx].1 == node && edges[idx].0 != node then
      1 + CountInDegreeHelper(edges, node, idx + 1)
    else
      CountInDegreeHelper(edges, node, idx + 1)
  }

  function UpdateInDegreeHelper(degrees: seq<int>, edges: seq<(int, int)>, node: int, processed: int, idx: int): int
    requires 0 <= node < |degrees|
    requires 0 <= idx <= |edges|
    decreases |edges| - idx
  {
    if idx == |edges| then degrees[node]
    else if edges[idx].0 == processed && edges[idx].1 == node && node != processed then
      UpdateInDegreeHelper(degrees, edges, node, processed, idx + 1) - 1
    else
      UpdateInDegreeHelper(degrees, edges, node, processed, idx + 1)
  }

  function FindMinUnprocessedWithZeroInDegree(n: int, processed: seq<bool>, in_degree: seq<int>): int
    requires |processed| == n
    requires |in_degree| == n
    ensures FindMinUnprocessedWithZeroInDegree(n, processed, in_degree) == -1 ||
            0 <= FindMinUnprocessedWithZeroInDegree(n, processed, in_degree) < n
  {
    FindMinHelper(n, processed, in_degree, 0, -1)
  }

  function FindMinHelper(n: int, processed: seq<bool>, in_degree: seq<int>, idx: int, result: int): int
    requires 0 <= idx <= n
    requires |processed| == n
    requires |in_degree| == n
    requires result == -1 || (0 <= result < idx && !processed[result] && in_degree[result] == 0)
    ensures FindMinHelper(n, processed, in_degree, idx, result) == -1 ||
            0 <= FindMinHelper(n, processed, in_degree, idx, result) < n
    decreases n - idx
  {
    if idx == n then result
    else if !processed[idx] && in_degree[idx] == 0 then
      if result == -1 || idx < result then
        FindMinHelper(n, processed, in_degree, idx + 1, idx)
      else
        FindMinHelper(n, processed, in_degree, idx + 1, result)
    else
      FindMinHelper(n, processed, in_degree, idx + 1, result)
  }
}
