"""Write a hash inventory from explicitly staged/tracked distribution paths."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    paths = subprocess.check_output(['git', 'ls-files', '-z'], cwd=ROOT).decode().split('\0')
    files = []
    for name in sorted(p for p in paths if p and p != 'MANIFEST.json'):
        path = ROOT / name
        raw = path.read_bytes()
        files.append({'path': name, 'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()})
    (ROOT / 'MANIFEST.json').write_text(json.dumps({
        'algorithm': 'SHA-256', 'scope': 'All staged/tracked distribution files except this inventory itself; text is LF.',
        'files': files}, indent=2) + '\n', encoding='utf-8', newline='\n')
    print(f'Inventoried {len(files)} files')


if __name__ == '__main__':
    main()
