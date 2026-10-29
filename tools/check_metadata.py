"""CFF schema validation and consistent paper/companion metadata (PyYAML/jsonschema)."""
import argparse
import hashlib
import json
from pathlib import Path
import yaml
import jsonschema

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('cff_schema', type=Path, help='Official CFF 1.2.0 schema JSON')
    args = parser.parse_args()
    schema_raw = args.cff_schema.read_bytes()
    schema = json.loads(schema_raw)
    citation = yaml.safe_load((ROOT / 'CITATION.cff').read_text(encoding='utf-8'))
    jsonschema.validators.validator_for(schema)(schema).validate(citation)
    software = json.loads((ROOT / '.zenodo.json').read_text())
    paper = json.loads((ROOT / 'publication/zenodo-paper.json').read_text())['metadata']
    preferred = citation['preferred-citation']
    assert citation['title'] == software['title']
    assert preferred['title'] == paper['title']
    assert citation['version'] == software['version'] == paper['version']
    assert citation['license'] == software['license'] == 'Apache-2.0'
    assert paper['license'] == 'CC-BY-4.0'
    assert preferred['authors'] == citation['authors']
    a = citation['authors'][0]
    assert software['creators'] == paper['creators'] == [{
        'name': a['family-names'] + ', ' + a['given-names'],
        'affiliation': a['affiliation'], 'orcid': a['orcid'].rsplit('/', 1)[1]}]
    assert software['upload_type'] == 'software'
    assert paper['upload_type'] == 'publication' and paper['publication_type'] == 'preprint'
    assert 'doi' not in citation and preferred['doi'] == '10.5281/zenodo.23754698' and 'date-released' not in citation
    result = {'status': 'pass', 'cff_schema_sha256': hashlib.sha256(schema_raw).hexdigest(),
              'cff_schema_id': schema.get('$id', schema.get('id')),
              'zenodo_check': 'Documented field types/roles and author/title/license/version consistency; not an ingestion test.',
              'preferred_citation_verified_paper_doi': preferred['doi']}
    output = ROOT / 'build/metadata.json'
    output.parent.mkdir(exist_ok=True)
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
