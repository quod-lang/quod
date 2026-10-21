def normalize_path(p: str) -> str:
    absolute = p.startswith("/")
    kept = []
    for comp in p.split("/"):
        if comp == "" or comp == ".":
            continue
        if comp == "..":
            if kept and kept[-1] != "..":
                kept.pop()
            elif not absolute:
                kept.append(comp)
            continue
        kept.append(comp)
    if absolute:
        return "/" + "/".join(kept)
    return "/".join(kept) if kept else "."
