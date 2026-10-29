"""Independent finite checks for S175's joint sector/norm estimator."""
import ast
import hashlib
import json
import random
import time
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
import sector_norm_sampling as sn
from sector_norm_sampling import cc, qr, pd, ss
from check_sector_cubic_sampling import determinant_family
from check_cubic_centroid_controls import transform_physical
from check_frobenius_trace_degree import fast_independent_probability
from check_corrupted_field_contractions import check_native
from check_shared_control_anchors import ConstantCoins
from check_two_copy_control_anchors import all_displacements

ROOT = Path(__file__).resolve().parents[1]
COUNTS = {}


def bump(key, count=1):
    COUNTS[key] = COUNTS.get(key, 0) + count


def z4value(poly, x):
    return sum(v for m, v in poly.items() if (x & m) == m) % 4


def dense_gaussian(poly, width):
    counts = [0, 0, 0, 0]
    for x in range(1 << width):
        counts[z4value(poly, x)] += 1
    return counts[0]-counts[2], counts[1]-counts[3]


def primitive_checks(rng):
    for n in range(9):
        for _ in range(24):
            phase = sn.equatorial_phase(n, rng.getrandbits(2*n+n*(n-1)//2))
            sn.add4(phase, 0, rng.randrange(4))
            assert sn.gaussian4(phase, n) == dense_gaussian(phase, n)
            bump('independent_z4_gaussian_sums')
            dim = min(n+1, 7)
            forms = [(rng.getrandbits(dim), rng.getrandbits(1)) for _ in range(n)]
            pulled = sn.substitute4(phase, forms)
            for x in range(1 << dim):
                image = sum((((row & x).bit_count() % 2)^constant) << j
                            for j, (row, constant) in enumerate(forms))
                assert z4value(pulled, x) == z4value(phase, image)
                bump('independent_z4_affine_values')


def dense_sector(prepared, sector):
    """Construct small vectors directly from the unconditioned source phases."""
    cert = prepared['norm_sector']
    r, c = cert['rank'], cert['sectors']
    size, root = 1 << r, 1 << (r//2)
    value = lambda poly, y, t: (-1)**cc.anf_evaluate(poly, sector | (y << c) | (t << (c+r)))
    psi0 = [value(cert['state_phase'], y, 0) for y in range(size)]
    psi1 = [value(cert['partner_phase'], 0, t) for t in range(size)]
    kernel = [[value(cert['kernel_phase'], y, t) for y in range(size)] for t in range(size)]
    # Check the entire real Clifford kernel, not only its asserted cross rank.
    for t in range(size):
        for u in range(size):
            assert sum(a*b for a,b in zip(kernel[t], kernel[u])) == (size if t == u else 0)
    applied = [sum(a*b for a,b in zip(row, psi0)) for row in kernel]
    cross = Fraction(sum(a*b for a,b in zip(psi1, applied)), size*root)
    reference = Fraction(ss.branch_sum(prepared, sector), prepared['sector_cubic']['branch_denominator'])
    assert cross == reference and abs(cross) <= 1
    numerators = [root*a+b for a,b in zip(psi1, applied)]
    norm = Fraction(sum(a*a for a in numerators), size*size)
    assert norm == 2+2*cross
    bump('independent_dense_sector_operator_and_norm')
    if norm == 0:
        bump('exact_zero_norm_sector')
    return numerators, norm, cross


def direct_norm_numerator(numerators, r, word):
    phase = sn.equatorial_phase(r, word)
    parts = [0, 0, 0, 0]
    for t, value in enumerate(numerators):
        parts[z4value(phase, t)] += value
    return (parts[0]-parts[2])**2 + (parts[1]-parts[3])**2


def exhaustive_moments(rng):
    sources = [
        ['cubic-field-v1', 1, [1], [[], []], 0, 0],
        ['cubic-field-v1', 3, [1,2,4], [[7], [7]], 3, 0],
        ['cubic-field-v1', 4, [1,2,4,8], [[14,3,8], [7,9]], 5, 0],
        ['cubic-field-v1', 5, [1,2,4,8,16], [[14,19,12,16], [7,25]], 3, 0],
    ]
    records = []
    for desc in sources:
        prepared = sn.prepare(ss.reduce_source(desc, 2, 2, rng))
        cert = prepared['norm_sector']
        assert cert['accepted']
        r, c, bits = cert['rank'], cert['sectors'], cert['equatorial_bits']
        assert r <= 4
        ensemble, den = 1 << bits, cert['norm_denominator']
        total_mean, total_second = Fraction(0), Fraction(0)
        for sector in range(1 << c):
            vector, norm, cross = dense_sector(prepared, sector)
            values = [direct_norm_numerator(vector, r, word) for word in range(ensemble)]
            mean = Fraction(sum(values), ensemble*den)
            second = Fraction(sum(v*v for v in values), ensemble*den*den)
            assert mean == norm
            assert second == 2*norm*norm-Fraction(sum(v**4 for v in vector), den*den)
            assert second-mean*mean <= norm*norm
            for word in range(ensemble) if r <= 2 else [rng.randrange(ensemble) for _ in range(40)]:
                assert sn.norm_numerator(prepared, sector, word) == values[word]
                bump('production_norm_against_independent_dense_vectors')
            total_mean += mean/2-1
            total_second += second/4-mean+1
            bump('exhaustive_equatorial_moment_points', ensemble)
            bump('exact_conditional_moment_identities')
        total_mean /= 1 << c
        total_second /= 1 << c
        assert total_second-total_mean**2 <= 4
        p = fast_independent_probability(desc)
        assert (1-total_mean)/2 == p
        native = cc.compile_native(desc)
        check_native(native, p)
        records.append(dict(qubits=desc[1], rank=r, controls=cert['controls'],
                            eta=prepared['matching']['eta'], sectors=1 << c,
                            ensemble=ensemble, probability=str(p),
                            joint_variance=str(total_second-total_mean**2)))
    return records


def native_outputs(rng):
    cases = []
    for t, flip, mixed, hidden in [(2,False,False,False), (2,True,False,True),
                                   (2,False,True,False)]:
        desc, p = determinant_family(t, flip, mixed)
        if mixed:
            desc[4] = 5
        if hidden:
            desc = transform_physical(desc, rng)
        cases.append((desc, 1, f'determinant_t{t}_flip{flip}_mixed{mixed}_hidden{hidden}'))
    cases.extend([
        (['cubic-field-v1', 5, [1,2,4,8,16], [[14,19,12,16], [7,25]], 3, 0], 2, 'rank4_nonzero_input'),
        (['cubic-field-v1', 4, [1,2,4,8], [[14,3,8], [7,9]], 5, 0], 2, 'matching_offset'),
        (['cubic-field-v1', 3, [1,2,4], [[7], [3]], 0, 0], 0, 'exact_shortcut'),
        (all_displacements(2, 2), 2, 'two_controls'),
        (['cubic-field-v1', 11, list(cc.identity(11)),
          [[14,112,896,264], [1|(1 << j)|(1 << (j+1)) for j in range(1,11,2)]],
          13, 0], 3, 'three_controls'),
    ])
    results = []
    for index, (desc, Q, label) in enumerate(cases):
        native = cc.compile_native(desc)
        source_start = time.perf_counter()
        original = ss.reduce_native(desc[1], native['gates'], desc[4], desc[5], Q, 2, rng)
        source_seconds = time.perf_counter()-source_start
        prepare_start = time.perf_counter()
        prepared = sn.prepare(original)
        prepare_seconds = time.perf_counter()-prepare_start
        assert prepared['sector_cubic']['accepted'], label
        probability = fast_independent_probability(desc)
        if desc[1] <= 8:
            check_native(native, probability)
        # Small b is an actual full run; large-b tests below only audit/refuse schedules.
        b = 2 if index == 3 else 1
        start = time.perf_counter()
        with patch.object(ss, 'branch_sum', side_effect=AssertionError('4^k sector fallback forbidden')):
            answer = sn.evaluate_source(prepared, b, random.Random(175100+index))
        norm_seconds = time.perf_counter()-start
        assert abs(answer['estimate']-probability) <= Fraction(1, 1 << b)
        assert answer['stats']['gaussian_sums'] == answer['plan']['gaussian_sum_bound']
        bump('complete_original_native_outputs')
        old_start = time.perf_counter()
        old_answer = ss.evaluate_source(original, b, random.Random(175100+index))
        old_seconds = time.perf_counter()-old_start
        assert abs(old_answer['estimate']-probability) <= Fraction(1, 1 << b)
        assert old_answer['failure_probability'] == answer['failure_probability']
        bump('matched_original_reader_outputs')
        if answer['mode'] == 'sector_norm_sampling':
            for high_b in (1, 7, 257, 4096):
                plan = sn.evaluation_plan(prepared, high_b)
                assert plan['samples'] == 32*(1 << (2*high_b))*(2*prepared['failure_bits']+3)
                tape = ConstantCoins(0)
                refused = sn.evaluate_source(prepared, high_b, tape, max_samples=0)
                assert refused['mode'] == 'budget_refused' and tape.calls == 0
                bump('precision_schedule_and_predraw_refusals')
        results.append(dict(label=label, qubits=desc[1], source_bits=native['source_bits'],
                            descriptor=desc, control_cap=Q,
                            source_records=len(native['gates']), rank=prepared['norm_sector']['rank'],
                            controls=prepared['norm_sector']['controls'], bits=b, failure_bits=2,
                            mode=answer['mode'], reference=str(probability), estimate=str(answer['estimate']),
                            plan={k: str(v) if isinstance(v, Fraction) else v for k,v in answer['plan'].items()},
                            stats=answer['stats'], source_discovery_seconds=source_seconds,
                            norm_preparation_seconds=prepare_seconds, norm_readout_seconds=norm_seconds,
                            baseline=dict(mode=old_answer['mode'], estimate=str(old_answer['estimate']),
                                          gaussian_sums=old_answer['stats']['gaussian_sums'],
                                          random_bits=old_answer['stats']['random_bits'],
                                          readout_seconds=old_seconds),
                            timing_scope='Shared native recognition/discovery timed once; separate preparation/readout. '
                                         'Single local observations, not a performance benchmark.'))
        print('Native output passed:', label, flush=True)
    return results


def main():
    rng = random.Random(17520261028)
    primitive_checks(rng)
    print('Z4 sums and affine pullbacks pass', flush=True)
    moments = exhaustive_moments(rng)
    print('Exhaustive norm moments and source identities pass', flush=True)
    native = native_outputs(rng)
    # A genuine cap-one refusal and an unsupported word stay explicit misses.
    for desc in [all_displacements(2, 2),
                 ['cubic-field-v1', 3, [1,2,4], [[7],[7],[7]], 0, 0]]:
        tape = ConstantCoins(0)
        result = sn.prepare(ss.reduce_source(desc, 1, 2, tape))
        assert not result['norm_sector']['accepted']
        answer = sn.evaluate_source(result, 2, tape)
        assert answer['mode'] == 'discovery_miss'
        bump('explicit_discovery_or_grammar_refusals')
    paths = ['src/sector_norm_sampling.py', 'src/check_sector_norm_sampling.py',
             'src/sector_cubic_sampling.py', 'src/affine_control_sampling.py', 'src/output_displacement_sums.py']
    hashes = {}
    for path in paths:
        raw = (ROOT/path).read_bytes()
        ast.parse(raw.decode())
        hashes[path] = dict(sha256=hashlib.sha256(raw).hexdigest(),
                           canonical_lf_sha256=hashlib.sha256(raw.replace(b'\r\n', b'\n')).hexdigest())
    receipt = dict(status='pass', baseline='75694fa51add1c5293168349c4d29af9ef4030ea',
                   seed=17520261028, counts=COUNTS, exact_moments=moments, native_outputs=native, hashes=hashes,
                   scope='Finite exact checks of source-to-sector norm integration, published equatorial moments, '
                         'Gaussian-integer arithmetic and complete capped native runs. High-b checks only audit '
                         'schedules and refuse before draws. No novelty, universal simulation or Lean certification.')
    target = ROOT/'artifacts/s175-sector-norm-checks.json'
    target.parent.mkdir(exist_ok=True)
    target.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps(dict(status='pass', counts=COUNTS, receipt=str(target)), indent=2), flush=True)


if __name__ == '__main__':
    main()
