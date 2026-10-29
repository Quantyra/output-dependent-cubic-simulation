"""Run the exact finite checker in isolation and compare non-timing evidence."""
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
RECEIPT = Path('artifacts/s175-sector-norm-checks.json')


def stable(value):
    if isinstance(value, list):
        return [stable(v) for v in value]
    if isinstance(value, dict):
        return {k: stable(v) for k, v in value.items()
                if not k.endswith('_seconds') and k != 'sha256'}
    return value


def main():
    frozen = json.loads((ROOT / RECEIPT).read_text(encoding='utf-8'))
    with tempfile.TemporaryDirectory(prefix='sector-paper-check-') as directory:
        temporary = Path(directory)
        shutil.copytree(ROOT / 'src', temporary / 'src', ignore=shutil.ignore_patterns('__pycache__'))
        (temporary / 'artifacts').mkdir()
        command = ('import runpy,sys; sys.path.insert(0,"src"); '
                   'runpy.run_path("src/check_sector_norm_sampling.py",run_name="__main__")')
        subprocess.run([sys.executable, '-u', '-c', command], cwd=temporary, check=True)
        actual = json.loads((temporary / RECEIPT).read_text(encoding='utf-8'))
        assert stable(actual) == stable(frozen), 'Reproduced mathematical evidence differs'
        output = ROOT / 'build/reproduction.json'
        output.parent.mkdir(exist_ok=True)
        output.write_text(json.dumps({'status': 'pass', 'python': sys.version.split()[0],
            'comparison': 'All fields except *_seconds and raw sha256 match; canonical-LF hashes match.',
            'counts': actual['counts'], 'regenerated_receipt': actual}, indent=2) + '\n', encoding='utf-8')
        print('Reproduction PASS: all mathematical fields and canonical source hashes match.')


if __name__ == '__main__':
    main()
