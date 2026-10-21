module Solution {
  predicate ValidWords(words: seq<string>, width: int)
  {
    forall i :: 0 <= i < |words| ==>
      0 < |words[i]| <= width && (forall j :: 0 <= j < |words[i]| ==> words[i][j] != ' ')
  }

  function Spaces(n: int): string
  {
    seq(if n < 0 then 0 else n, _ => ' ')
  }

  // number of further words fitting on the line, given current line length cur
  function More(rest: seq<string>, width: int, cur: int): nat
    ensures More(rest, width, cur) <= |rest|
    decreases |rest|
  {
    if |rest| == 0 || cur + 1 + |rest[0]| > width then 0
    else 1 + More(rest[1..], width, cur + 1 + |rest[0]|)
  }

  function Fit(ws: seq<string>, width: int): nat
    requires |ws| > 0
    ensures 1 <= Fit(ws, width) <= |ws|
  {
    1 + More(ws[1..], width, |ws[0]|)
  }

  function JoinSingle(ws: seq<string>): string
  {
    if |ws| == 0 then "" else if |ws| == 1 then ws[0] else ws[0] + " " + JoinSingle(ws[1..])
  }

  function LeftJ(ws: seq<string>, width: int): string
  {
    var s := JoinSingle(ws);
    s + Spaces(width - |s|)
  }

  function SumLen(ws: seq<string>): int
  {
    if |ws| == 0 then 0 else |ws[0]| + SumLen(ws[1..])
  }

  function BuildFull(ws: seq<string>, i: int, base: int, extra: int): string
    decreases |ws|
  {
    if |ws| == 0 then ""
    else if |ws| == 1 then ws[0]
    else ws[0] + Spaces(base + (if i < extra then 1 else 0)) + BuildFull(ws[1..], i + 1, base, extra)
  }

  function FullJ(ws: seq<string>, width: int): string
    requires |ws| >= 2
  {
    var total := width - SumLen(ws);
    var g := |ws| - 1;
    BuildFull(ws, 0, total / g, total % g)
  }

  function MakeLine(ws: seq<string>, width: int, isLast: bool): string
  {
    if isLast || |ws| < 2 then LeftJ(ws, width) else FullJ(ws, width)
  }

  function Justify(ws: seq<string>, width: int): seq<string>
    decreases |ws|
  {
    if |ws| == 0 then []
    else
      var k := Fit(ws, width);
      [MakeLine(ws[..k], width, k == |ws|)] + Justify(ws[k..], width)
  }

  method justify(words: seq<string>, width: int) returns (lines: seq<string>)
    requires ValidWords(words, width)
    ensures lines == Justify(words, width)
  {
    lines := [];
    var i := 0;
    while i < |words|
      invariant 0 <= i <= |words|
      invariant Justify(words, width) == lines + Justify(words[i..], width)
      decreases |words| - i
    {
      var rest := words[i..];
      var k := Fit(rest, width);
      var line := MakeLine(rest[..k], width, k == |rest|);
      assert rest[k..] == words[i + k..];
      lines := lines + [line];
      i := i + k;
    }
    assert words[i..] == [];
  }
}
