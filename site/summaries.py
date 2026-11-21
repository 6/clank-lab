"""Read public paper summaries by result slug."""

import json


def paper_summaries(checkout, slugs):
    try:
        entries = json.loads((checkout / "site" / "plain_summaries.json").read_text(encoding="utf-8"))
    except FileNotFoundError as error:
        raise ValueError("Missing site/plain_summaries.json") from error
    if not isinstance(entries, dict):
        raise ValueError("site/plain_summaries.json must map result slugs to strings")
    summaries, invalid = {}, []
    for slug in slugs:
        summary = entries.get(slug)
        if not isinstance(summary, str) or not summary.strip():
            invalid.append(slug)
        else:
            summaries[slug] = summary.strip()
    if invalid:
        raise ValueError("Missing, blank, or invalid plain_summary for " + ", ".join(sorted(invalid)))
    return summaries
