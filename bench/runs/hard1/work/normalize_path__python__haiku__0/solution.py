def normalize_path(p: str) -> str:
    is_absolute = p.startswith('/')
    components = p.split('/')

    kept = []

    for comp in components:
        if comp == '' or comp == '.':
            continue
        elif comp == '..':
            if kept and kept[-1] != '..':
                kept.pop()
                if not kept and not is_absolute:
                    kept.append('..')
            elif not is_absolute:
                kept.append(comp)
        else:
            kept.append(comp)

    if is_absolute:
        return '/' + '/'.join(kept)
    else:
        return '/'.join(kept) if kept else '.'
