"""Offline integrity, provenance and publication-boundary checks."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    manifest = json.loads((ROOT / 'MANIFEST.json').read_text(encoding='utf-8'))
    for item in manifest['files']:
        path = ROOT / item['path']
        assert path.is_file(), item['path']
        assert path.stat().st_size == item['bytes'], item['path']
        assert sha(path) == item['sha256'], item['path']
    provenance = json.loads((ROOT / 'PROVENANCE.json').read_text(encoding='utf-8'))
    for item in provenance['files']:
        assert sha(ROOT / item['path']) == item['sha256'], item['path']
        assert len(item['origin_snapshot']) == 40
        assert len(item['origin_last_change']) == 40
    modules = {p.stem: p for p in (ROOT / 'src').glob('*.py')}
    for path in modules.values():
        ast.parse(path.read_text(encoding='utf-8'))
    receipt = json.loads((ROOT / 'artifacts/s175-sector-norm-checks.json').read_text())
    assert receipt['status'] == 'pass'
    for path, hashes in receipt['hashes'].items():
        raw = (ROOT / path).read_bytes().replace(b'\r\n', b'\n')
        assert hashlib.sha256(raw).hexdigest() == hashes['canonical_lf_sha256'], path
    software = json.loads((ROOT / '.zenodo.json').read_text())
    paper = json.loads((ROOT / 'publication/zenodo-paper.json').read_text())['metadata']
    assert software['creators'] == paper['creators'] == [{
        'name': 'Fredriksen, Daniel', 'affiliation': 'Quantyra Inc.',
        'orcid': '0009-0002-9123-7435'}]
    assert software['upload_type'] == 'software' and software['license'] == 'Apache-2.0'
    assert paper['upload_type'] == 'publication' and paper['publication_type'] == 'preprint'
    assert paper['license'] == 'CC-BY-4.0'
    assert software['version'] == paper['version'] == '0.1.0'
    for obj in (software, paper):
        assert not any(k in obj for k in ('doi', 'prereserve_doi', 'publication_date'))
    assert (ROOT / 'manuscript/main.pdf').read_bytes().startswith(b'%PDF-')
    tex = (ROOT / 'manuscript/main.tex').read_text()
    for label in ('lem:walsh', 'prop:sector', 'lem:branches', 'thm:discovery',
                  'lem:moments', 'thm:estimator', 'prop:family'):
        assert '\\label{' + label + '}' in tex, label
    print(json.dumps({'status': 'pass', 'manifest_files': len(manifest['files']),
                      'origin_files': len(provenance['files']), 'source_modules': len(modules),
                      'paper_pdf_sha256': sha(ROOT / 'manuscript/main.pdf'),
                      'release_status': 'published paper DOI 10.5281/zenodo.23754698'}, indent=2))


if __name__ == '__main__':
    main()
