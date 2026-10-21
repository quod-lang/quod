def glob_match(pattern: str, text: str) -> bool:
    # Tokenize: ('*',), ('?',), or ('lit', ch)
    tokens = []
    i, n = 0, len(pattern)
    while i < n:
        c = pattern[i]
        if c == '\\':
            if i + 1 < n:
                tokens.append(('lit', pattern[i + 1]))
                i += 2
            else:
                tokens.append(('lit', '\\'))
                i += 1
        elif c == '*':
            if not tokens or tokens[-1] != ('*',):
                tokens.append(('*',))
            i += 1
        elif c == '?':
            tokens.append(('?',))
            i += 1
        else:
            tokens.append(('lit', c))
            i += 1

    # Greedy with backtracking to last star (linear-ish, correct for glob)
    t, p = 0, 0
    star_p, star_t = -1, 0
    m, tl = len(tokens), len(text)
    while t < tl:
        if p < m:
            tok = tokens[p]
            if tok[0] == '*':
                star_p, star_t = p, t
                p += 1
                continue
            if tok[0] == '?' or tok[1] == text[t]:
                p += 1
                t += 1
                continue
        if star_p >= 0:
            star_t += 1
            t = star_t
            p = star_p + 1
            continue
        return False
    while p < m and tokens[p][0] == '*':
        p += 1
    return p == m
