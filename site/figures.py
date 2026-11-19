"""Read the vetted paper figures and verify the exact SVG bytes."""

import hashlib
import json
from pathlib import Path
import re
import xml.etree.ElementTree as ET

FIGURES = json.loads(Path(__file__).with_name("figures.json").read_text(encoding="utf-8"))
FIGURE_FILE = "figure.svg"
SVG = "{http://www.w3.org/2000/svg}"


def verify_figure(data, entry):
    if hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise ValueError("SVG SHA-256 mismatch")
    if b"<!ENTITY" in data or re.search(rb"<\?(?!xml\s)", data):
        raise ValueError("Unexpected SVG entity or processing instruction")
    try:
        root = ET.fromstring(data)
    except ET.ParseError as error:
        raise ValueError("Invalid SVG") from error
    if root.tag != SVG + "svg":
        raise ValueError("Invalid SVG root")
    for element in root.iter():
        tag = element.tag.rsplit("}", 1)[-1].lower()
        if tag in {"script", "foreignobject", "a", "animate", "animatetransform", "animatemotion", "set"}:
            raise ValueError("Unexpected active SVG element")
        for attr, value in element.attrib.items():
            name = attr.rsplit("}", 1)[-1].lower()
            if name.startswith("on"):
                raise ValueError("Unexpected SVG event handler")
            if name == "href" and not (
                re.fullmatch(r"#[\w.-]+", value)
                or tag == "image" and re.fullmatch(r"data:image/png;base64,[a-zA-Z0-9+/=\s]+", value)
            ):
                raise ValueError("Unexpected SVG reference")


def read_figure(checkout, slug, entry):
    source = checkout / "results" / slug / entry["path"]
    data = source.read_bytes()
    verify_figure(data, entry)
    return data
