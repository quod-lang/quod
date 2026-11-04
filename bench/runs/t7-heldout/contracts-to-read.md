# Contracts of T7 for the author to read

Five accepted contracts per arm, drawn with `random.Random(20261105)` after the measure. The main measure and the judge have run; the code of each solution is left out where it can be.

## quod: arbitrate_field #2

Several engines propose a value for the same field. Each candidate is a triple `(engine, confidence, value)`, with `engine` an index into `rank` and `confidence` between 0 and 100; `threshold` is also between 0 and 100. `rank[e]` is the trust order of engine `e`: a smaller rank is more trusted. Return the index, in `candidates`, of the retained candidate: among the candidates whose confidence is at least `threshold`, the one with the highest confidence; between equal confidences, the one whose engine has the smallest rank; and between equal confidences and equal ranks, the first one. If no candidate reaches the threshold, return -1: the field goes to manual validation.

Measure: sound=True, exact=True. Whole file: `work/arbitrate_field__quod__claude-haiku-5-5__2/solution.quod`.

```
fn arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) -> int
  requires 0 <= threshold <= 100
  requires forall i in 0..len(candidates): 0 <= candidates[i].0 < len(rank)
  requires forall i in 0..len(candidates): 0 <= candidates[i].1 <= 100
  // -1 exactly when no candidate reaches the threshold
  ensures result >= -1 && result < len(candidates)
  ensures (result == -1) <==> (forall i in 0..len(candidates): candidates[i].1 < threshold)
  // otherwise the result is eligible and no other eligible candidate beats it
  ensures result >= 0 ==> (
    candidates[result].1 >= threshold &&
    forall j in 0..len(candidates):
      (j != result && candidates[j].1 >= threshold) ==>
        (candidates[j].1 < candidates[result].1 ||
         (candidates[j].1 == candidates[result].1 &&
          (rank[candidates[j].0] > rank[candidates[result].0] ||
           (rank[candidates[j].0] == rank[candidates[result].0] && j > result)))))
```

## quod: next_permutation #0

Given a list of integers (possibly empty, duplicates allowed), return the rearrangement of its elements that comes next in lexicographic order, that is the smallest rearrangement strictly greater than the list. If the list is its own greatest rearrangement, return the smallest one, its elements in non-decreasing order.

Measure: sound=True, exact=True. Whole file: `work/next_permutation__quod__claude-haiku-5-5__0/solution.quod`.

```
fn next_permutation(xs: seq<int>) -> seq<int>
  ensures result == next_model(xs)
```

## quod: next_permutation #1

Given a list of integers (possibly empty, duplicates allowed), return the rearrangement of its elements that comes next in lexicographic order, that is the smallest rearrangement strictly greater than the list. If the list is its own greatest rearrangement, return the smallest one, its elements in non-decreasing order.

Measure: sound=True, exact=True. Whole file: `work/next_permutation__quod__claude-haiku-5-5__1/solution.quod`.

```
fn next_permutation(xs: seq<int>) -> seq<int>
  ensures len(result) == len(xs)
  ensures forall k in 0..len(result): count(result, result[k]) == count(xs, result[k])
  ensures forall k in 0..len(xs) - 1: (xs[k] < xs[k + 1] && (forall j in k + 1..len(xs) - 1: xs[j] >= xs[j + 1])) ==> (result[..k] == xs[..k] && xs[k] < result[k] && (forall j in k + 1..len(xs): xs[j] > xs[k] ==> result[k] <= xs[j]) && (forall j in k + 1..len(xs) - 1: result[j] <= result[j + 1]))
  ensures (forall k in 0..len(xs) - 1: xs[k] >= xs[k + 1]) ==> (forall j in 0..len(result) - 1: result[j] <= result[j + 1])
```

## quod: split_folds #0

Given the classification of each page of a scanned batch, as a list of integers (0: a continuation page, 1: the first page of a document, 2: a separator sheet), return the folds of the batch, in order, as a list of pairs `(start, end)`: the fold covers the pages `start` to `end - 1`. A fold starts at a page classified 1, or at the first page that is not a separator, at the start of the batch or after a separator. It ends just before the next page classified 1, the next separator, or the end of the batch. Separator sheets belong to no fold, every other page belongs to exactly one, and no fold is empty.

Measure: sound=True, exact=True. Whole file: `work/split_folds__quod__claude-haiku-5-5__0/solution.quod`.

```
fn split_folds(pages: seq<int>) -> seq<(int, int)>
  requires forall k in 0..len(pages): 0 <= pages[k] <= 2
  ensures result == folds_from(pages, 0)
```

## quod: two_sum_sorted #2

Given a list of integers `xs` sorted in non-decreasing order (possibly empty, duplicates allowed) and an integer `target`, return a pair of indices `(i, j)` with `i < j` and `xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do.

Measure: sound=True, exact=False. Whole file: `work/two_sum_sorted__quod__claude-haiku-5-5__2/solution.quod`.

```
fn two_sum_sorted(xs: seq<int>, target: int) -> (int, int)
  requires forall a in 0..len(xs): forall b in a..len(xs): xs[a] <= xs[b]
  ensures result.0 == -1 ==>
    (result.1 == -1 && forall p in 0..len(xs): forall q in p + 1..len(xs): xs[p] + xs[q] != target)
  ensures result.0 != -1 ==>
    (0 <= result.0 && result.0 < result.1 && result.1 < len(xs)
     && xs[result.0] + xs[result.1] == target
     && (forall p in 0..result.0: forall q in p + 1..len(xs): xs[p] + xs[q] != target)
     && (forall q in result.1 + 1..len(xs): forall p in 0..q: xs[p] + xs[q] != target))
```

## quod-mcp: arbitrate_field #0

Several engines propose a value for the same field. Each candidate is a triple `(engine, confidence, value)`, with `engine` an index into `rank` and `confidence` between 0 and 100; `threshold` is also between 0 and 100. `rank[e]` is the trust order of engine `e`: a smaller rank is more trusted. Return the index, in `candidates`, of the retained candidate: among the candidates whose confidence is at least `threshold`, the one with the highest confidence; between equal confidences, the one whose engine has the smallest rank; and between equal confidences and equal ranks, the first one. If no candidate reaches the threshold, return -1: the field goes to manual validation.

Measure: sound=True, exact=True. Whole file: `work/arbitrate_field__quod-mcp__claude-haiku-5-5__0/solution.quod`.

```
fn arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) -> int
  requires forall i in 0..len(candidates): 0 <= candidates[i].0 < len(rank)
  requires forall i in 0..len(candidates): 0 <= candidates[i].1 <= 100
  requires 0 <= threshold <= 100
  ensures (result == -1 && forall i in 0..len(candidates): candidates[i].1 < threshold)
    || (0 <= result < len(candidates)
        && candidates[result].1 >= threshold
        && forall j in 0..len(candidates):
             candidates[j].1 >= threshold ==>
               (j == result || better(candidates, rank, result, j)))
  decreases len(candidates)
```

## quod-mcp: gcd #1

Return the greatest common divisor of two integers `a` and `b`, either of which may be negative or zero. The result is never negative, and the greatest common divisor of 0 and 0 is 0.

Measure: sound=True, exact=True. Whole file: `work/gcd__quod-mcp__claude-haiku-5-5__1/solution.quod`.

```
fn gcd(a: int, b: int) -> int
  ensures result >= 0
  ensures result == gcd_model(a, b)
```

## quod-mcp: next_permutation #1

Given a list of integers (possibly empty, duplicates allowed), return the rearrangement of its elements that comes next in lexicographic order, that is the smallest rearrangement strictly greater than the list. If the list is its own greatest rearrangement, return the smallest one, its elements in non-decreasing order.

Measure: sound=True, exact=True. Whole file: `work/next_permutation__quod-mcp__claude-haiku-5-5__1/solution.quod`.

```
fn next_permutation(xs: seq<int>) -> seq<int>
  ensures len(result) == len(xs)
  ensures forall i in 0..len(xs): cnt(result, xs[i]) == cnt(xs, xs[i])
  ensures forall j in 0..len(result): cnt(xs, result[j]) >= 1
  ensures (forall k in 0..len(xs) - 1: xs[k] >= xs[k + 1]) ==> (forall k in 0..len(xs) - 1: result[k] <= result[k + 1])
  ensures forall p in 0..len(xs) - 1: (xs[p] < xs[p + 1] && forall k in p + 1..len(xs) - 1: xs[k] >= xs[k + 1]) ==> ((forall i in 0..p: result[i] == xs[i]) && xs[p] < result[p] && (forall k in p + 1..len(xs): xs[k] > xs[p] ==> result[p] <= xs[k]) && (forall k in p + 1..len(xs) - 1: result[k] <= result[k + 1]))
```

## quod-mcp: transpose #2

Given a matrix as a list of rows, with at least one row, at least one column, and all rows of the same length, return its transpose: element `j` of row `i` of the result is element `i` of row `j` of the input.

Measure: sound=True, exact=True. Whole file: `work/transpose__quod-mcp__claude-haiku-5-5__2/solution.quod`.

```
fn transpose(m: seq<seq<int>>) -> seq<seq<int>>
  requires len(m) >= 1
  requires len(m[0]) >= 1
  requires forall i in 0..len(m): len(m[i]) == len(m[0])
  ensures len(result) == len(m[0])
  ensures forall j in 0..len(result): len(result[j]) == len(m)
  ensures forall j in 0..len(result): forall i in 0..len(m): result[j][i] == m[i][j]
```

## quod-mcp: two_sum_sorted #1

Given a list of integers `xs` sorted in non-decreasing order (possibly empty, duplicates allowed) and an integer `target`, return a pair of indices `(i, j)` with `i < j` and `xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do.

Measure: sound=True, exact=True. Whole file: `work/two_sum_sorted__quod-mcp__claude-haiku-5-5__1/solution.quod`.

```
fn two_sum_sorted(xs: seq<int>, target: int) -> (int, int)
  requires forall k in 0..len(xs) - 1: xs[k] <= xs[k + 1]
  ensures
    (result.0 == -1 && result.1 == -1
      && forall p in 0..len(xs): forall q in 0..len(xs): !(p < q && xs[p] + xs[q] == target))
    || (0 <= result.0 && result.0 < result.1 && result.1 < len(xs)
      && xs[result.0] + xs[result.1] == target)
  loose (a, b) => (a.0 == -1) == (b.0 == -1)
```

## dafny: arbitrate_field #2

Several engines propose a value for the same field. Each candidate is a triple `(engine, confidence, value)`, with `engine` an index into `rank` and `confidence` between 0 and 100; `threshold` is also between 0 and 100. `rank[e]` is the trust order of engine `e`: a smaller rank is more trusted. Return the index, in `candidates`, of the retained candidate: among the candidates whose confidence is at least `threshold`, the one with the highest confidence; between equal confidences, the one whose engine has the smallest rank; and between equal confidences and equal ranks, the first one. If no candidate reaches the threshold, return -1: the field goes to manual validation.

Measure: sound=True, exact=True. Whole file: `work/arbitrate_field__dafny__claude-haiku-5-5__2/solution.dfy`.

```
method arbitrate_field(candidates: seq<(int, int, int)>, rank: seq<int>, threshold: int) returns (r: int)
    requires 0 <= threshold <= 100
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].0 < |rank|
    requires forall i :: 0 <= i < |candidates| ==> 0 <= candidates[i].1 <= 100
    ensures r == -1 || 0 <= r < |candidates|
    // No candidate reaches the threshold: manual validation.
    ensures r == -1 ==> forall i :: 0 <= i < |candidates| ==> candidates[i].1 < threshold
    // Otherwise the result is eligible and beats every other eligible candidate
    // (highest confidence, then smallest engine rank, then first index).
    ensures r != -1 ==> candidates[r].1 >= threshold
    ensures r != -1 ==> forall i :: 0 <= i < |candidates| && candidates[i].1 >= threshold ==>
      candidates[i].1 < candidates[r].1 ||
      (candidates[i].1 == candidates[r].1 && rank[candidates[i].0] > rank[candidates[r].0]) ||
      (candidates[i].1 == candidates[r].1 && rank[candidates[i].0] == rank[candidates[r].0] && i >= r)
```

## dafny: gcd #2

Return the greatest common divisor of two integers `a` and `b`, either of which may be negative or zero. The result is never negative, and the greatest common divisor of 0 and 0 is 0.

Measure: sound=None, exact=None. Whole file: `work/gcd__dafny__claude-haiku-5-5__2/solution.dfy`.

```
method gcd(a: int, b: int) returns (r: int)
    ensures r >= 0
    ensures a == 0 && b == 0 ==> r == 0
    ensures !(a == 0 && b == 0) ==> r > 0 && a % r == 0 && b % r == 0
    ensures !(a == 0 && b == 0) ==> forall d: int :: IsCommonDivisor(d, a, b) ==> d <= r
```

## dafny: transpose #1

Given a matrix as a list of rows, with at least one row, at least one column, and all rows of the same length, return its transpose: element `j` of row `i` of the result is element `i` of row `j` of the input.

Measure: sound=True, exact=True. Whole file: `work/transpose__dafny__claude-haiku-5-5__1/solution.dfy`.

```
method transpose(m: seq<seq<int>>) returns (r: seq<seq<int>>)
    requires |m| >= 1
    requires |m[0]| >= 1
    requires IsRectangular(m)
    ensures |r| == |m[0]|
    ensures forall i :: 0 <= i < |r| ==> |r[i]| == |m|
    ensures forall i, j :: 0 <= i < |r| && 0 <= j < |r[i]| ==> r[i][j] == m[j][i]
```

## dafny: two_sum_sorted #0

Given a list of integers `xs` sorted in non-decreasing order (possibly empty, duplicates allowed) and an integer `target`, return a pair of indices `(i, j)` with `i < j` and `xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do.

Measure: sound=True, exact=True. Whole file: `work/two_sum_sorted__dafny__claude-haiku-5-5__0/solution.dfy`.

```
method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires forall a: int, b: int :: 0 <= a < b < |xs| ==> xs[a] <= xs[b]
    ensures r.0 == -1 ==> r.1 == -1 && (forall a: int, b: int :: 0 <= a < b < |xs| ==> xs[a] + xs[b] != target)
    ensures r.0 != -1 ==> 0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
```

## dafny: two_sum_sorted #2

Given a list of integers `xs` sorted in non-decreasing order (possibly empty, duplicates allowed) and an integer `target`, return a pair of indices `(i, j)` with `i < j` and `xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do.

Measure: sound=True, exact=True. Whole file: `work/two_sum_sorted__dafny__claude-haiku-5-5__2/solution.dfy`.

```
method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires forall p, q :: 0 <= p < q < |xs| ==> xs[p] <= xs[q]
    ensures r == (-1, -1) ==> forall p, q :: 0 <= p < q < |xs| ==> xs[p] + xs[q] != target
    ensures r != (-1, -1) ==> 0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
```

## dafny-loop: gcd #0

Return the greatest common divisor of two integers `a` and `b`, either of which may be negative or zero. The result is never negative, and the greatest common divisor of 0 and 0 is 0.

Measure: sound=True, exact=True. Whole file: `work/gcd__dafny-loop__claude-haiku-5-5__0/solution.dfy`.

```
method gcd(a: int, b: int) returns (r: int)
    ensures r == GcdSpec(a, b)
    ensures r >= 0
    ensures a == 0 && b == 0 ==> r == 0
```

## dafny-loop: next_permutation #0

Given a list of integers (possibly empty, duplicates allowed), return the rearrangement of its elements that comes next in lexicographic order, that is the smallest rearrangement strictly greater than the list. If the list is its own greatest rearrangement, return the smallest one, its elements in non-decreasing order.

Measure: sound=None, exact=None. Whole file: `work/next_permutation__dafny-loop__claude-haiku-5-5__0/solution.dfy`.

```
method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures multiset(r) == multiset(xs)
    ensures NonIncr(xs) ==> NonDecr(r)
    ensures !NonIncr(xs) ==> forall k :: IsPivot(xs, k) ==> IsNext(xs, r, k)
```

## dafny-loop: next_permutation #1

Given a list of integers (possibly empty, duplicates allowed), return the rearrangement of its elements that comes next in lexicographic order, that is the smallest rearrangement strictly greater than the list. If the list is its own greatest rearrangement, return the smallest one, its elements in non-decreasing order.

Measure: sound=None, exact=None. Whole file: `work/next_permutation__dafny-loop__claude-haiku-5-5__1/solution.dfy`.

```
method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures multiset(r) == multiset(xs)
    ensures Desc(xs) ==> Sorted(r)
    ensures !Desc(xs) ==> exists k :: IsNextAt(xs, r, k)
```

## dafny-loop: next_permutation #2

Given a list of integers (possibly empty, duplicates allowed), return the rearrangement of its elements that comes next in lexicographic order, that is the smallest rearrangement strictly greater than the list. If the list is its own greatest rearrangement, return the smallest one, its elements in non-decreasing order.

Measure: sound=None, exact=None. Whole file: `work/next_permutation__dafny-loop__claude-haiku-5-5__2/solution.dfy`.

```
method next_permutation(xs: seq<int>) returns (r: seq<int>)
    ensures IsPerm(r, xs)
    ensures (exists p :: IsPerm(p, xs) && LexLt(xs, p)) ==>
              (LexLt(xs, r) && forall p :: IsPerm(p, xs) && LexLt(xs, p) ==> !LexLt(p, r))
    ensures !(exists p :: IsPerm(p, xs) && LexLt(xs, p)) ==> NonDecreasing(r)
```

## dafny-loop: two_sum_sorted #0

Given a list of integers `xs` sorted in non-decreasing order (possibly empty, duplicates allowed) and an integer `target`, return a pair of indices `(i, j)` with `i < j` and `xs[i] + xs[j] == target`, or `(-1, -1)` if there is none. Any such pair will do.

Measure: sound=True, exact=True. Whole file: `work/two_sum_sorted__dafny-loop__claude-haiku-5-5__0/solution.dfy`.

```
method two_sum_sorted(xs: seq<int>, target: int) returns (r: (int, int))
    requires sorted(xs)
    ensures r == (-1, -1) ==>
      forall a, b :: 0 <= a < b < |xs| ==> xs[a] + xs[b] != target
    ensures r != (-1, -1) ==>
      0 <= r.0 < r.1 < |xs| && xs[r.0] + xs[r.1] == target
```
