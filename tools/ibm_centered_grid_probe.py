"""Exploratory reflected-clock IBM finite-grid energies; NOT a proof.

The two source-energy formulas are from IBMRawGridSecondChaos.  The clock
coefficient is half endpoint minus folded-clock total variation.  Monte Carlo
statistics and the plug-in Cauchy--Schwarz ratio are not certified bounds.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
from pathlib import Path
import time

import numpy as np


def energies(radius: np.ndarray, *, check_direct: bool = False) -> tuple[float, float]:
    if (radius.ndim != 1 or radius.size < 2 or not np.isfinite(radius).all()
            or (radius < 0).any() or radius[0] != 0):
        raise ValueError("Need a finite nonnegative radius sequence starting at zero")
    gram = np.minimum.outer(radius, radius)
    increment_gram = np.diff(np.diff(gram, axis=0), axis=1)
    terminal = np.diff(gram[-1])
    q = 0.5 * (radius[-1] ** 2 - 2 * np.sum(terminal ** 2)
               + np.sum(increment_gram ** 2))
    if check_direct:
        left = gram[:-1, :-1]
        mixed = gram[1:, :-1] - left
        direct = np.sum(increment_gram * left + mixed * mixed.T)
        np.testing.assert_allclose(q, direct, rtol=1e-10, atol=1e-10)
    if q < -1e-9:
        raise AssertionError(f"Negative source energy: {q}")
    clock = 0.5 * (radius[-1] - radius[0] - np.sum(np.abs(np.diff(radius))))
    return float(q), float(clock)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=512)
    parser.add_argument("--max-grid", type=int, default=512)
    parser.add_argument("--seed", type=int, default=1498)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.samples < 2 or args.max_grid < 16 or args.max_grid & (args.max_grid - 1):
        parser.error("Need samples>=2 and a power-of-two max-grid>=16")
    start = time.perf_counter()
    # Deterministic normalization checks, independently of simulated paths.
    for r in [0.0, 0.5, 1.0, 2.0]:
        q, b = energies(np.array([0.0, r, 0.0]), check_direct=True)
        np.testing.assert_allclose([q, b], [2 * r * r, -r])
        np.testing.assert_allclose(energies(np.array([0.0, r]), check_direct=True)[0], 0)
    rng = np.random.default_rng(args.seed)
    increments = rng.normal(size=(args.samples, args.max_grid)) / np.sqrt(args.max_grid)
    paths = np.concatenate([np.zeros((args.samples, 1)), np.cumsum(increments, axis=1)], axis=1)
    rows = []
    n = 16
    while n <= args.max_grid:
        radii = np.abs(paths[:, ::args.max_grid // n])
        data = np.array([energies(r, check_direct=(i < 4)) for i, r in enumerate(radii)])
        q_mean = float(data[:, 0].mean())
        b_var = float(data[:, 1].var(ddof=1))
        rows.append(dict(
            grid=n, source_energy_mean=q_mean,
            source_energy_mean_sample_se=float(data[:, 0].std(ddof=1) / np.sqrt(args.samples)),
            source_energy_over_sqrt_grid=q_mean / np.sqrt(n),
            clock_mean=float(data[:, 1].mean()), clock_sample_variance=b_var,
            estimated_ratio_NOT_CERTIFIED=q_mean / np.sqrt(q_mean + b_var),
        ))
        n *= 2
    result = dict(
        status="EXPLORATORY_MONTE_CARLO_ONLY_NOT_A_PROOF",
        seed=args.seed, samples=args.samples, horizon=1, numpy_version=np.__version__,
        shared_paths=True, direct_formula_checks_per_grid=4,
        deterministic_loop_and_one_step_checks=8, rows=rows,
        wall_seconds=time.perf_counter() - start,
        time_utc=dt.datetime.now(dt.timezone.utc).isoformat(),
    )
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
