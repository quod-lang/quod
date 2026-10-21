def utf8_valid(bs: list[int]) -> bool:
    i = 0
    while i < len(bs):
        b = bs[i]

        # Single byte character (0xxxxxxx): 0-127
        if b < 0x80:
            i += 1
        # Continuation byte at start is invalid
        elif b < 0xC0:
            return False
        # Two-byte character (110xxxxx 10xxxxxx)
        elif b < 0xE0:
            if i + 1 >= len(bs):
                return False

            cp = (b & 0x1F) << 6
            b2 = bs[i + 1]

            if (b2 & 0xC0) != 0x80:
                return False

            cp |= (b2 & 0x3F)

            # Check for overlong encoding
            if cp < 0x80:
                return False

            i += 2
        # Three-byte character (1110xxxx 10xxxxxx 10xxxxxx)
        elif b < 0xF0:
            if i + 2 >= len(bs):
                return False

            cp = (b & 0x0F) << 12

            b2 = bs[i + 1]
            if (b2 & 0xC0) != 0x80:
                return False
            cp |= (b2 & 0x3F) << 6

            b3 = bs[i + 2]
            if (b3 & 0xC0) != 0x80:
                return False
            cp |= (b3 & 0x3F)

            # Check for overlong encoding
            if cp < 0x800:
                return False

            # Check for surrogate code points
            if 0xD800 <= cp <= 0xDFFF:
                return False

            i += 3
        # Four-byte character (11110xxx 10xxxxxx 10xxxxxx 10xxxxxx)
        elif b < 0xF8:
            if i + 3 >= len(bs):
                return False

            cp = (b & 0x07) << 18

            b2 = bs[i + 1]
            if (b2 & 0xC0) != 0x80:
                return False
            cp |= (b2 & 0x3F) << 12

            b3 = bs[i + 2]
            if (b3 & 0xC0) != 0x80:
                return False
            cp |= (b3 & 0x3F) << 6

            b4 = bs[i + 3]
            if (b4 & 0xC0) != 0x80:
                return False
            cp |= (b4 & 0x3F)

            # Check for overlong encoding
            if cp < 0x10000:
                return False

            # Check for values exceeding U+10FFFF
            if cp > 0x10FFFF:
                return False

            i += 4
        # Invalid start byte
        else:
            return False

    return True
