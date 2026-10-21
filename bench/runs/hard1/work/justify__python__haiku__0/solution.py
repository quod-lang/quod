def justify(words: list[str], width: int) -> list[str]:
    if not words:
        return []

    # Step 1: Greedily pack words into lines
    lines = []
    current_line = []
    current_length = 0

    for word in words:
        if not current_line:
            current_line.append(word)
            current_length = len(word)
        elif current_length + 1 + len(word) <= width:
            # Word fits with one space before it
            current_line.append(word)
            current_length += 1 + len(word)
        else:
            # Word doesn't fit, start a new line
            lines.append(current_line)
            current_line = [word]
            current_length = len(word)

    if current_line:
        lines.append(current_line)

    # Step 2: Justify each line
    result = []
    for i, line in enumerate(lines):
        if i == len(lines) - 1:
            # Last line: left-justified
            justified = ' '.join(line).ljust(width)
        elif len(line) == 1:
            # Single word line: left-justified
            justified = line[0].ljust(width)
        else:
            # Multiple words, not the last line: distribute spaces
            total_chars = sum(len(word) for word in line)
            total_spaces = width - total_chars
            gaps = len(line) - 1
            spaces_per_gap = total_spaces // gaps
            extra_spaces = total_spaces % gaps

            justified = ""
            for j, word in enumerate(line):
                justified += word
                if j < len(line) - 1:
                    # Add spaces after this word
                    spaces = spaces_per_gap
                    if j < extra_spaces:
                        spaces += 1
                    justified += ' ' * spaces

        result.append(justified)

    return result
