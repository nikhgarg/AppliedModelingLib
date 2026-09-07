#!/usr/bin/env python3
"""Check the exact deployed website, its local links, and legacy entry points."""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
from html.parser import HTMLParser
from pathlib import Path
import time
from urllib.parse import unquote, urljoin, urlsplit, urlunsplit
from urllib.request import Request, urlopen


class Document(HTMLParser):
    def __init__(self, text):
        super().__init__()
        self.links, self.ids = [], set()
        self.feed(text)

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if attrs.get('id'):
            self.ids.add(attrs['id'])
        for name in ('href', 'src'):
            if attrs.get(name):
                self.links.append(attrs[name])


def local_links(root: Path, base_url: str):
    """Resolve generated documents before making any network requests."""
    base_url = base_url.rstrip('/') + '/'
    base = urlsplit(base_url)
    targets = {p.relative_to(root).as_posix(): set() for p in root.rglob('*.html')}
    for path in sorted(root.rglob('*.html')):
        page_url = urljoin(base_url, path.relative_to(root).as_posix())
        for href in Document(path.read_text()).links:
            parsed = urlsplit(urljoin(page_url, href))
            if (parsed.scheme, parsed.netloc) != (base.scheme, base.netloc):
                continue
            if not parsed.path.startswith(base.path):
                continue
            relative = unquote(parsed.path[len(base.path):])
            if not relative or relative.endswith('/'):
                relative += 'index.html'
            target = (root / relative).resolve()
            if not target.is_relative_to(root.resolve()) or not target.is_file():
                raise ValueError(f'{path.relative_to(root)}: missing local target {href}')
            if parsed.fragment:
                if target.suffix == '.html' and unquote(parsed.fragment) not in Document(target.read_text()).ids:
                    raise ValueError(f'{path.relative_to(root)}: missing anchor {href}')
            targets.setdefault(relative, set()).add(unquote(parsed.fragment))
    return targets


def fetch(url):
    with urlopen(Request(url, headers={'User-Agent': 'AppliedModelingLib-deployment-check'}), timeout=30) as response:
        return response.geturl(), response.read()


def check(root: Path, base_url: str, *, fetcher=fetch):
    targets = local_links(root, base_url)
    base_url = base_url.rstrip('/') + '/'
    # Exact bytes prevent an old successful deployment from passing the check.
    def verify(relative):
        expected = (root / relative).read_bytes()
        stamp = hashlib.sha256(expected).hexdigest()[:16]
        url = urljoin(base_url, relative) + '?deployment=' + stamp
        last = None
        for attempt in range(4):
            try:
                _, actual = fetcher(url)
                if actual != expected:
                    raise ValueError(f'Deployed bytes differ: {relative}')
                return
            except Exception as exc:
                last = exc
                if attempt < 3:
                    time.sleep(5)
        raise RuntimeError(f'{relative}: {last}')
    with ThreadPoolExecutor(max_workers=8) as pool:
        list(pool.map(verify, sorted(targets)))
    return len(targets)


def check_legacy(base_url: str, *, fetcher=fetch):
    base = urlsplit(base_url)
    old_site = urlunsplit((base.scheme, base.netloc, '/EconCSLib/', '', ''))
    final, body = fetcher(old_site)
    destination = base_url.rstrip('/') + '/'
    # The legacy Pages path uses a source-owned browser redirect.
    text = body.decode('utf-8', errors='replace')
    if not final.startswith(destination) and not any(
        pattern in text for pattern in (
            'url=' + destination,
            'location.replace("' + destination,
            "location.replace('" + destination,
        )
    ):
        raise ValueError('Legacy site does not redirect to the current project site')
    for suffix in ('', '/blob/main/papers/LG24ServiceLevelAgreements/FINAL_VALIDATION_REPORT.md'):
        final, _ = fetcher('https://github.com/nikhgarg/EconCSLib' + suffix)
        if not final.startswith('https://github.com/nikhgarg/AppliedModelingLib' + suffix):
            raise ValueError('Legacy GitHub entry point no longer resolves: ' + suffix)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-dir', type=Path, required=True)
    parser.add_argument('--base-url', required=True)
    parser.add_argument('--check-legacy', action='store_true')
    args = parser.parse_args()
    count = check(args.build_dir.resolve(), args.base_url)
    if args.check_legacy:
        check_legacy(args.base_url)
    print(f'Deployed website verified: {count} exact files; local links and anchors resolve.')
    if args.check_legacy:
        print('Legacy site and GitHub redirects verified.')


if __name__ == '__main__':
    main()
