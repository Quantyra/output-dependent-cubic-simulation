"""Check exact Lean helper axiom reports against the allowed baseline."""
import re
import sys
from pathlib import Path

EXPECTED = {
    'SectorSimulation.booleanDerivative_shift_invariant': set(),
    'SectorSimulation.binaryShift_involutive': {'Quot.sound'},
    'SectorSimulation.binaryDerivative_shift_invariant': {'Quot.sound'},
    'SectorSimulation.evalPhase_empty': set(),
    'SectorSimulation.evalPhase_duplicate_cancel': {'propext'},
    'SectorSimulation.secondPhaseDerivative_shift_invariant': {'Quot.sound'},
    'SectorSimulation.booleanDerivative_xor': {'propext'},
    'SectorSimulation.phaseFold_from': {'propext'},
    'SectorSimulation.evalPhase_append': {'propext', 'Quot.sound'},
    'SectorSimulation.phaseDerivative_append': {'propext', 'Quot.sound'},
    'SectorSimulation.booleanDerivative_const': set(),
    'SectorSimulation.booleanDerivative_and': {'propext'},
    'SectorSimulation.binaryVariable_derivative': {'propext'},
    'SectorSimulation.quadratic_difference_expansion': set(),
    'SectorSimulation.cubic_difference_expansion': set(),
    'SectorSimulation.quadraticVariable_derivative': set(),
    'SectorSimulation.cubicVariable_derivative': set(),
    'SectorSimulation.evalMonomial_eq_true_iff': {'propext', 'Quot.sound'},
    'SectorSimulation.evalMonomial_emptyMask': {'propext', 'Quot.sound'},
    'SectorSimulation.evalMonomial_selectedVariables': {'propext', 'Quot.sound'},
    'SectorSimulation.monomialDegree_eq_selectedLength': set(),
    'SectorSimulation.list_length_le_three_shape': {'propext'},
    'SectorSimulation.cubicMask_selected_shape': {'propext'},
    'SectorSimulation.evalMonomial_selected_nil': {'propext', 'Quot.sound'},
    'SectorSimulation.evalMonomial_selected_one': {'propext', 'Quot.sound'},
    'SectorSimulation.evalMonomial_selected_two': {'propext', 'Quot.sound'},
    'SectorSimulation.evalMonomial_selected_three': {'propext', 'Quot.sound'},
    'SectorSimulation.evalQuadraticTerms_append': {'propext'},
    'SectorSimulation.evalConditionalQuadraticTerm': {'propext'},
    'SectorSimulation.evalLinearDerivativeTerms': {'propext'},
    'SectorSimulation.evalQuadraticDerivativeTerms': {'propext'},
    'SectorSimulation.evalCubicDerivativeTerms': {'propext'},
    'SectorSimulation.cubicMaskDerivativeTerms_correct': {'propext', 'Quot.sound'},
    'SectorSimulation.cubicPhaseDerivativeTerms_correct': {'propext', 'Quot.sound'},
}


def main():
    if len(sys.argv) != 2:
        raise SystemExit('usage: python tools/check_lean_audit.py AUDIT_OUTPUT')
    output = Path(sys.argv[1]).read_text(encoding='utf-8')
    reports = re.findall(r"'([^']+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])", output)
    assert len(reports) == len(EXPECTED), f'Unexpected number of reports: {reports}'
    found = {}
    for name, axioms in reports:
        assert name not in found, f'Duplicate axiom report: {name}'
        found[name] = {a.strip() for a in axioms.split(',') if a.strip()}
    assert found == EXPECTED, f'Axiom baseline mismatch: {found}'
    assert 'sorryAx' not in output, 'Unproved Lean axiom detected'
    print('Lean helper axiom audit passed; this does not certify a manuscript theorem.')


if __name__ == '__main__':
    main()
