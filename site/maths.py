"""TeX delimiters and static MathML rendering with KaTeX."""

import html
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess

def split_math(text):
    """Yield (source, TeX or None, display) without consuming literal dollars.

    Single-dollar math follows the usual currency/whitespace rules: no space
    after the opener or before the closer, and no digit after the closer.
    Backslash escapes and balanced braces protect delimiters inside TeX.
    """
    start = cursor = 0
    delimiters = (("$$", "$$", True), (r"\(", r"\)", False),
                  (r"\[", r"\]", True), ("$", "$", False))
    while cursor < len(text):
        match = next((d for d in delimiters if text.startswith(d[0], cursor)), None)
        if match is not None:
            left, right, display = match
            begin = cursor + len(left)
            end, depth = begin, 0
            if left != "$" or begin < len(text) and not text[begin].isspace():
                while end < len(text):
                    if depth == 0 and text.startswith(right, end):
                        if left == "$" and (end == begin or text[end - 1].isspace()
                                            or end + 1 < len(text) and text[end + 1].isdigit()):
                            break
                        if end > begin:
                            if start < cursor:
                                yield text[start:cursor], None, False
                            stop = end + len(right)
                            yield text[cursor:stop], text[begin:end], display
                            cursor = start = stop
                            break
                    if text[end] == "\\":
                        end += 2
                        continue
                    if text[end] == "{":
                        depth += 1
                    elif text[end] == "}":
                        depth = max(0, depth - 1)
                    end += 1
                if cursor == start and cursor > begin:
                    continue
        # Escaped dollars and backslashes cannot open math.
        cursor += 2 if text[cursor] == "\\" else 1
    if start < len(text):
        yield text[start:], None, False


def has_math(text):
    return any(tex is not None for _, tex, _ in split_math(text))


class MathHTML(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.parts = []
        self.expressions = []

    def handle_starttag(self, tag, attrs):
        self.parts.append(self.get_starttag_text())

    def handle_startendtag(self, tag, attrs):
        self.parts.append(self.get_starttag_text())

    def handle_endtag(self, tag):
        self.parts.append(f"</{tag}>")

    def handle_data(self, text):
        for source, tex, display in split_math(text):
            if tex is None:
                # Retain literal escaped dollars without showing the TeX escape.
                self.parts.append(re.sub(
                    r"(\\+)\$",
                    lambda match: match[1][:-1] + '<span class="tex-dollar">$</span>'
                    if len(match[1]) % 2 else match[0], html.escape(source)))
            else:
                self.parts.append(len(self.expressions))
                self.expressions.append(dict(tex=tex, display=display))


def render_html(source):
    """Render only body text; attributes, document titles and metadata stay text."""
    parser = MathHTML()
    parser.feed(source)
    parser.close()
    rendered = []
    if parser.expressions:
        script = Path(__file__).with_name("render-math.cjs")
        try:
            result = subprocess.run(["node", str(script)], input=json.dumps(parser.expressions),
                                    capture_output=True, text=True, timeout=60)
        except FileNotFoundError as error:
            raise ValueError("Node.js is required to render math at build time") from error
        except subprocess.TimeoutExpired as error:
            raise ValueError("KaTeX rendering timed out") from error
        if result.returncode:
            raise ValueError("KaTeX rendering failed: " + result.stderr.strip())
        rendered = json.loads(result.stdout)
    return "".join(rendered[part] if isinstance(part, int) else part for part in parser.parts)
