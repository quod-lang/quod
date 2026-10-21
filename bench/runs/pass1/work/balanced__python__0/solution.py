def balanced(s: str) -> bool:
    pairs = {')': '(', ']': '[', '}': '{'}
    openers = set(pairs.values())
    stack = []
    for ch in s:
        if ch in openers:
            stack.append(ch)
        elif ch in pairs:
            if not stack or stack.pop() != pairs[ch]:
                return False
    return not stack
