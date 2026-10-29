"""Check the published statement inventory without claiming a formal proof."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    source = (ROOT / 'manuscript/main.tex').read_text(encoding='utf-8')
    manifest = json.loads((ROOT / 'lean/CLAIMS.json').read_text(encoding='utf-8'))
    pattern = r'\\begin\{(?:theorem|lemma|proposition|corollary)\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}'
    published = re.findall(pattern, source)
    assert published, 'No published theorem-like labels found'
    assert len(published) == len(set(published)), 'Duplicate paper statement label'
    claims = manifest['claims']
    identifiers = [c['id'] for c in claims]
    assert len(identifiers) == len(set(identifiers)), 'Duplicate claim identifier'
    missing = sorted(set(published) - set(identifiers))
    assert not missing, f'Published statements absent from inventory: {missing}'
    allowed = set(manifest['status_vocabulary'])
    for claim in claims:
        assert claim['status'] in allowed, claim['id']
        for field in ('section', 'assumptions', 'quantifiers', 'statement', 'unresolved_bridge'):
            assert claim.get(field), (claim['id'], field)
        assert isinstance(claim.get('dependencies'), list), claim['id']
        if claim['status'] == 'proved and kernel checked':
            assert claim.get('target') and claim.get('build_audit_receipt'), claim['id']
            assert (ROOT / claim['build_audit_receipt']).is_file(), claim['id']
    print(json.dumps({'status': 'pass', 'paper_theorem_labels': published,
                      'inventory_entries': len(claims),
                      'paper_theorems_proved': [c['id'] for c in claims
                          if c['id'] in published and c['status'] == 'proved and kernel checked'],
                      'scope': 'Inventory coverage and receipt presence; not a proof or semantic equivalence check.'}, indent=2))


if __name__ == '__main__':
    main()
