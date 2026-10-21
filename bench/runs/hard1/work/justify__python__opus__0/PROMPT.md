Implement the function below in Python 3, in the file `solution.py` in the current directory.

## Specification
Fully justify text. `words` is a list of non-empty words (no spaces), each of length <= `width`. Greedily pack as many words as possible on each line with at least one space between words, so that each line has exactly `width` characters. On every line except the last, if the line has two or more words, distribute the spaces as evenly as possible between words, giving the extra spaces to the leftmost gaps. A line with a single word, and the last line, are left-justified: words separated by one space, padded with spaces on the right up to `width`. Return the list of lines (empty list for no words).

## Required signature
```python
def justify(words: list[str], width: int) -> list[str]
```

## Rules
- Standard library only. The function must be defined at module top level in `solution.py`.
- You may write and run your own tests (`python` is available). Run commands directly in the current directory (no `cd`, no chained commands).
- When you are confident the implementation is correct, stop.
  It will be evaluated against hidden tests.
