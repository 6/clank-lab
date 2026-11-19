"""Locate paper source folders at the public checkout's release tags."""

import re
import subprocess

REPOSITORY = "https://github.com/6/clank-lab"


def paper_release_links(checkout, slugs):
    """Map each tagged result to the folder at its highest numbered release."""
    git = ["git", "-C", str(checkout)]
    refs = subprocess.run(
        git + ["for-each-ref", "--format=%(refname:strip=2)", "refs/tags"],
        capture_output=True, text=True,
    )
    if refs.returncode:
        raise ValueError("Cannot read release tags from the public Git checkout")

    slugs = set(slugs)
    latest = {}
    for tag in refs.stdout.splitlines():
        match = re.fullmatch(r"(.+)-v([1-9][0-9]*)", tag)
        if match is None:
            continue
        slug, number = match.groups()
        version = int(number)
        if slug in slugs and version > latest.get(slug, (0, ""))[0]:
            latest[slug] = version, tag

    links = {}
    for slug, (_, tag) in latest.items():
        folder = f"results/{slug}"
        result = subprocess.run(
            git + ["cat-file", "-t", f"refs/tags/{tag}^{{commit}}:{folder}"],
            capture_output=True, text=True,
        )
        if result.returncode or result.stdout.strip() != "tree":
            raise ValueError(f"Release tag {tag} is missing the {folder} directory")
        links[slug] = f"{REPOSITORY}/tree/{tag}/{folder}"
    return links
