def glob_match(pattern: str, text: str) -> bool:
    memo = {}

    def helper(p_idx, t_idx):
        if (p_idx, t_idx) in memo:
            return memo[(p_idx, t_idx)]

        # Base case: both pattern and text exhausted
        if p_idx == len(pattern) and t_idx == len(text):
            return True

        # Base case: pattern exhausted but text remaining
        if p_idx == len(pattern):
            return False

        # Base case: text exhausted but pattern remaining
        if t_idx == len(text):
            # Check if remaining pattern can match empty string
            result = True
            idx = p_idx
            while idx < len(pattern):
                if pattern[idx] == '*':
                    idx += 1
                elif pattern[idx] == '\\':
                    if idx + 1 == len(pattern):
                        # Lone backslash at end - can't match empty
                        result = False
                        break
                    else:
                        # Escaped character - can't match empty
                        result = False
                        break
                else:
                    # Literal character - can't match empty
                    result = False
                    break
            memo[(p_idx, t_idx)] = result
            return result

        # General case: both pattern and text have characters
        if pattern[p_idx] == '\\':
            if p_idx + 1 < len(pattern):
                # Escaped character
                if pattern[p_idx + 1] == text[t_idx]:
                    result = helper(p_idx + 2, t_idx + 1)
                else:
                    result = False
            else:
                # Lone backslash at the end
                if text[t_idx] == '\\':
                    result = helper(p_idx + 1, t_idx + 1)
                else:
                    result = False
        elif pattern[p_idx] == '*':
            # Match 0 or more characters
            result = helper(p_idx + 1, t_idx) or helper(p_idx, t_idx + 1)
        elif pattern[p_idx] == '?':
            # Match exactly one character
            result = helper(p_idx + 1, t_idx + 1)
        else:
            # Literal character
            if pattern[p_idx] == text[t_idx]:
                result = helper(p_idx + 1, t_idx + 1)
            else:
                result = False

        memo[(p_idx, t_idx)] = result
        return result

    return helper(0, 0)
