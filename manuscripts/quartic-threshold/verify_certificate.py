"""Check certificate transcription and rational margin; not the Lean interval engine."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import ast
import hashlib
import json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-root', type=Path, default=Path(__file__).resolve().parents[2])
    args = parser.parse_args()
    dossier = json.loads((Path(__file__).parent / 'source-assessment.json').read_text(encoding='utf-8'))
    certificate = dossier['certificate_transcription']
    source_path = args.source_root / certificate['source_file']
    source = source_path.read_text(encoding='utf-8')
    text_hash = hashlib.sha256(source.encode('utf-8')).hexdigest()
    if text_hash != certificate['source_text_sha256']:
        raise RuntimeError('Certificate source differs from the frozen text; use its baseline checkout.')
    raw = source.split('def data : List (List (ℤ × ℤ)) := ', 1)[1].split('\ndef lo ', 1)[0]
    cells = [[list(pair) for pair in row] for row in ast.literal_eval(raw.strip())]
    if cells != certificate['cell_endpoint_numerators']:
        raise RuntimeError('Endpoint transcription differs from the source.')
    if len(cells) != 160 or any(len(row) != 3 for row in cells):
        raise RuntimeError('Unexpected certificate shape.')
    sums = [[sum(row[k][b] for row in cells) for b in range(2)] for k in range(3)]
    if sums != certificate['independently_resummed_numerators']:
        raise RuntimeError('Endpoint sums differ.')
    denominator = int(certificate['denominator'])
    error = F(161, 10**16)
    upper0 = F(sums[0][1], denominator) + error
    upper2 = F(sums[2][1], denominator) + error
    bound1 = max(abs(F(sums[1][0], denominator)), abs(F(sums[1][1], denominator))) + error
    if not (upper0 < 0 and upper2 < 0):
        raise RuntimeError('Expected negative derivative enclosures.')
    margin = bound1**2 - (-upper0)*(-upper2)
    if not (margin < -F(2, 10**20) and str(margin) == certificate['exact_laguerre_upper_bound']):
        raise RuntimeError('Laguerre margin check failed.')
    a = F(8, 5)
    bounds = [
        F(384) * F(2, 5)**50 < F(1, 10**17),
        8*a**4 + 111*a < F(3, 2)*F(5, 2)**6,
        F(176, 100)*F(1, 2)**160 + a*F(1, 10**17) < F(1, 10**16),
        F(2*10**22, 17*200**17) < F(1, 10**16),
    ]
    if not all(bounds):
        raise RuntimeError('Analytic-budget rational arithmetic check failed.')
    print(json.dumps(dict(status='PASSED', cells=160, channels=3,
                          endpoint_sums=sums, exact_laguerre_upper_bound=str(margin),
                          source_text_sha256=text_hash,
                          full_lean_or_interval_engine_rerun=False), indent=2))


if __name__ == '__main__':
    main()
