def justify(words: list[str], width: int) -> list[str]:
    lines = []
    i = 0
    n = len(words)
    while i < n:
        j = i + 1
        length = len(words[i])
        while j < n and length + 1 + len(words[j]) <= width:
            length += 1 + len(words[j])
            j += 1
        line_words = words[i:j]
        if j == n or len(line_words) == 1:
            line = " ".join(line_words)
            line += " " * (width - len(line))
        else:
            gaps = len(line_words) - 1
            total_spaces = width - sum(len(w) for w in line_words)
            base, extra = divmod(total_spaces, gaps)
            parts = []
            for k, w in enumerate(line_words[:-1]):
                parts.append(w)
                parts.append(" " * (base + (1 if k < extra else 0)))
            parts.append(line_words[-1])
            line = "".join(parts)
        lines.append(line)
        i = j
    return lines
