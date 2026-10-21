module Solution {
  method justify(words: seq<string>, width: int) returns (lines: seq<string>)
    requires width > 0
    requires forall w :: w in words ==> 0 < |w| <= width
    ensures forall line :: line in lines ==> |line| == width
  {
    if |words| == 0 {
      return [];
    }

    var result: seq<string> := [];
    var current_words: seq<string> := [];
    var i := 0;

    while i < |words|
      invariant 0 <= i <= |words|
      invariant forall j :: 0 <= j < |result| ==> |result[j]| == width
      decreases |words| - i
    {
      var word := words[i];
      if |current_words| == 0 {
        current_words := [word];
      } else {
        var current_len := compute_length(current_words);
        var spaces_min := |current_words|;
        if current_len + spaces_min + |word| <= width {
          current_words := current_words + [word];
        } else {
          var line := make_line(current_words, width, false);
          result := result + [line];
          current_words := [word];
        }
      }
      i := i + 1;
    }

    if |current_words| > 0 {
      var last_line := make_line(current_words, width, true);
      result := result + [last_line];
    }

    return result;
  }

  function compute_length(words: seq<string>): int
    requires |words| > 0
  {
    if |words| == 1 then |words[0]| else |words[0]| + compute_length(words[1..])
  }

  function make_line(words: seq<string>, width: int, is_last: bool): string
    requires |words| > 0
    requires width > 0
    ensures |make_line(words, width, is_last)| == width
  {
    if |words| == 1 then
      pad_to_width(words[0], width)
    else if is_last then
      var text := join_with_spaces(words, 0);
      pad_to_width(text, width)
    else
      var justified := build_justified(words, width);
      if |justified| == width then justified
      else pad_to_width(justified, width)
  }

  function join_with_spaces(words: seq<string>, idx: int): string
    requires |words| > 0
    requires 0 <= idx < |words|
    decreases |words| - idx
  {
    if idx == |words| - 1 then words[idx]
    else words[idx] + " " + join_with_spaces(words, idx + 1)
  }

  function pad_to_width(s: string, width: int): string
    requires width > 0
    ensures |pad_to_width(s, width)| == width
  {
    if |s| >= width then s[..width]
    else s + spaces(width - |s|)
  }

  function spaces(n: int): string
    requires n >= 0
    ensures |spaces(n)| == n
    decreases n
  {
    if n == 0 then "" else " " + spaces(n - 1)
  }

  function build_justified(words: seq<string>, width: int): string
    requires |words| > 1
    requires width > 0
  {
    var word_len := compute_length(words);
    var gaps := |words| - 1;
    var total_space := width - word_len;
    var base := if total_space <= 0 then 0 else total_space / gaps;
    var extra := if total_space <= 0 then 0 else total_space % gaps;
    assemble_line(words, 0, base, extra)
  }

  function assemble_line(words: seq<string>, idx: int, base: int, extra: int): string
    requires |words| > 0
    requires 0 <= idx < |words|
    requires base >= 0
    requires extra >= 0
    decreases |words| - idx
  {
    if idx == |words| - 1 then
      words[idx]
    else
      var sp := base + (if idx < extra then 1 else 0);
      words[idx] + spaces(sp) + assemble_line(words, idx + 1, base, extra)
  }
}
