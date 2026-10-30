"""Check the integrity and import completeness of this source bundle.

* every file listed in SHA256SUMS.json is present with the recorded hash;
* every import of a local module (one under the roots of provenance/LOCAL_MODULES.json) is present;
* the Lake requirements in lakefile.toml match the revisions pinned in lake-manifest.json.
"""
from pathlib import Path
import hashlib
import json
import re

root = Path(__file__).resolve().parent
hashes = json.loads((root / 'SHA256SUMS.json').read_text(encoding='utf-8'))
bad = [name for name, digest in hashes.items()
       if not (root / name).is_file()
       or hashlib.sha256((root / name).read_bytes()).hexdigest() != digest]
if bad:
    raise SystemExit('Missing or changed files: ' + ', '.join(bad))

IMPORT = re.compile(r'^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+([^\r\n]+)', re.M)
records = json.loads((root / 'provenance/LOCAL_MODULES.json').read_text(encoding='utf-8'))
modules = {r['module']: r['path'] for r in records}
roots = {name.split('.')[0] for name in modules}
absent = [path for path in modules.values() if not (root / path).is_file()]
if absent:
    raise SystemExit('Missing module sources: ' + ', '.join(absent))
for name, path in modules.items():
    text = (root / path).read_text(encoding='utf-8-sig')
    for match in IMPORT.finditer(text):
        for dep in match.group(1).split():
            if dep.startswith('--'):
                break
            if dep.split('.')[0] in roots and dep not in modules:
                raise SystemExit(f'Missing dependency of {name}: {dep}')
unlisted = [p.relative_to(root).as_posix() for r in sorted(roots) for p in (root / r).rglob('*.lean')
            if p.relative_to(root).as_posix() not in set(modules.values())]
if unlisted:
    raise SystemExit('Lean sources missing from provenance/LOCAL_MODULES.json: ' + ', '.join(unlisted))

# Lake requirements and the manifest
lakefile = (root / 'lakefile.toml').read_text(encoding='utf-8')
manifest = json.loads((root / 'lake-manifest.json').read_text(encoding='utf-8'))
pinned = {p['name']: p for p in manifest['packages'] if not p.get('inherited')}
requires = lakefile.split('[[require]]')[1:]
for block in requires:
    block = block.split('[[')[0]
    field = {k: v for k, v in re.findall(r'^(\w+)\s*=\s*"([^"]*)"', block, re.M)}
    p = pinned.get(field.get('name'))
    if p is None or p['url'] != field.get('git') or p['rev'] != field.get('rev'):
        raise SystemExit(f'lakefile.toml requirement {field.get("name")} does not match lake-manifest.json')
if len(requires) != len(pinned):
    raise SystemExit('lake-manifest.json pins packages that lakefile.toml does not require')
print(f'Verified {len(hashes)} distributed files and the imports of {len(modules)} local modules.')
