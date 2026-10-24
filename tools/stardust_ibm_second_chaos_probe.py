"""Private, empirical probe of UNPROJECTED conditional source-chaos energies.

No Lean theorem or intrinsic projected-output bound follows from this script.
It samples a standard folded Brownian clock and integrates the Gaussian
scenery analytically using the finite covariance identities audited in1484.
"""
from __future__ import annotations

import argparse
import datetime
import json
import time
from pathlib import Path

import numpy as np


def probe(samples: int = 256, seed: int = 1484) -> dict:
    start = time.perf_counter()
    sizes = [16, 64, 256, 1024]
    largest = sizes[-1]
    rng = np.random.default_rng(seed)
    paths = np.concatenate(
        [np.zeros((samples, 1)), np.cumsum(rng.standard_normal((samples, largest)), axis=1)
         / np.sqrt(largest)], axis=1
    )
    rows = []
    for size in sizes:
        energies = []
        field_energies = []
        residuals = []
        endpoint_errors = []
        for path in paths:
            levels = np.abs(path[:: largest // size])
            kernel = np.minimum.outer(levels, levels)
            gram = kernel[1:, 1:] - kernel[1:, :-1] - kernel[:-1, 1:] + kernel[:-1, :-1]
            mixed = kernel[1:, :-1] - kernel[:-1, :-1]
            field_energy = float(np.sum(gram * kernel[:-1, :-1]))
            direct = field_energy + float(np.sum(mixed * mixed.T))
            terminal_pairings = np.minimum(levels[-1], levels[1:]) - np.minimum(levels[-1], levels[:-1])
            endpoint = 0.5 * float(levels[-1] ** 2)
            energy = endpoint - float(np.sum(terminal_pairings ** 2)) + 0.5 * float(np.sum(gram ** 2))
            residual = abs(energy - direct)
            if residual > 1e-9 * (1 + abs(energy) + abs(direct)):
                raise AssertionError((size, energy, direct, residual))
            if min(energy, direct, field_energy) < -1e-9:
                raise AssertionError((size, energy, direct, field_energy))
            energies.append(energy)
            field_energies.append(field_energy)
            residuals.append(residual)
            endpoint_errors.append(energy - endpoint)
        a = np.asarray(energies)
        b = np.asarray(field_energies)
        rows.append(dict(
            intervals=size, samples=samples,
            source_value_energy_mean=float(a.mean()),
            source_value_energy_standard_error=float(a.std(ddof=1) / np.sqrt(samples)),
            source_field_energy_mean=float(b.mean()),
            source_field_energy_standard_error=float(b.std(ddof=1) / np.sqrt(samples)),
            source_value_energy_over_sqrt_intervals=float(a.mean() / np.sqrt(size)),
            maximum_two_formula_residual=float(max(residuals)),
            mean_error_if_quadratic_channel_is_dropped=float(np.mean(endpoint_errors)),
        ))
    return dict(
        status="EMPIRICAL_ONLY_NOT_A_PROOF", scope="UNPROJECTED source value/field energies; NOT intrinsic projected output",
        clock="standard Brownian finite grid, folded by absolute value; horizon1",
        coupling="same finest-grid paths subsampled at every resolution",
        seed=seed, dtype="float64", numpy_version=np.__version__, device="CPU",
        conclusion_limitations="Finite samples do not prove growth rates, divergence, convergence, or projection behavior.",
        timestamp_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
        wall_seconds=time.perf_counter() - start, rows=rows,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=256)
    parser.add_argument("--seed", type=int, default=1484)
    args = parser.parse_args()
    if args.samples < 2:
        parser.error("samples must be at least2")
    result = probe(args.samples, args.seed)
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
