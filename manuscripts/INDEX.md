# Manuscript catalog

The independent publication branch contains reviewed editorial drafts built from frozen verified mathematics. A reviewed draft has a current compiled PDF, visual-review receipt, and theorem map; it is not an external release or a novelty certification.

## Reviewed editorial papers

| Paper | Read and inspect | Scope and status |
|---|---|---|
| Quartic normal equations: complete-space solvability, sharp inverse stability, and atomic obstructions | [PDF](quartic-normal/main.pdf) · [LaTeX](quartic-normal/main.tex) · [theorem map](quartic-normal/theorem-map.json) · [editorial status](quartic-normal/editorial-status.md) | Nine pages. Arbitrary-measure L4 embedding with a positive lower bound; complete-space solvability, exponent 1/3, weighted regularity, and optimal exponent at every infinite Poisson datum. Full proofs. Reviewed draft; novelty unresolved. Frozen baseline `bab688bb6140cd6316c80680095a914ea0d346db`. |
| Endpoint singularities and nonreal zeros in fractional theta deformations | [PDF](fractional-theta-zeros/main.pdf) · [LaTeX](fractional-theta-zeros/main.tex) · [theorem map](fractional-theta-zeros/theorem-map.json) · [editorial status](fractional-theta-zeros/editorial-status.md) | Ten pages. Full endpoint asymptotic for 1<a<2, t≠0; finite real/infinite nonreal zeros; uniform order convergence; exact compact-escape hypotheses. Reviewed draft; novelty unresolved. Same frozen baseline. |

See the [editorial inventory](EDITORIAL_INVENTORY.md) for ranked mathematical contributions, consolidation decisions, literature limitations and deferred papers. Current PDFs have hash-linked build and visual receipts in their respective directories.

## Preserved earlier working notes

The following existing drafts and historical verification descriptions are retained. Their original scopes, dates and limitations are preserved; they have not been silently promoted to reviewed research papers.

### Original draft catalog

| Title | Source and readable PDF | Verification status | Latest revision |
|---|---|---|---|
| Clock Regularity and Hybrid Reconstruction for Actual Iterated Brownian Motion | [LaTeX](ibm-clock-hybrid/main.tex) · [PDF](ibm-clock-hybrid/main.pdf) | Actual completed Fourier source means, folded/collision gradients in the ORIGINAL clock graph, unique finite-horizon hidden-Brownian-clock reconstruction and original intrinsic joint divergence with a STATIC source channel. Exact sine counterexample distinguishes mean from full observable. Observed-filtration causality/full physical-time calculus remain OPEN. Two-pass local compilation SUCCEEDED; all5 rendered pages inspected; notation, references and source/PDF hashes verified. | Revision1, October25,2026; mathematical baselinec3381683f4d7abad527dee9575f4cf57deea0431, through checkpoint1520. |
| Signed Simpson Calculus for Reflected-Clock Iterated Brownian Motion | [LaTeX](ibm-signed-simpson/main.tex) · [PDF](ibm-signed-simpson/main.pdf) | Original verified1383–1394 scope retained. Revision2 corrects stale open labels: deterministic nonseparable C1-time/C4-space chain rule with explicit joint continuity, common-grid prefix maximum and Bernstein continuous-path supremum-norm convergence in probability are now verified. Bernstein smoothing is not asserted causal. Full adapted/nonsmooth IBM calculus remains OPEN. Two-pass local compilation SUCCEEDED; all6 current rendered pages inspected, notation legible, references resolved and hashes verified. | Revision2, October25,2026; original baseline072793e54f7a08ba39afc4919ea987d11e5c69e2; later status audited against checkpoint1520/c3381683f4d7abad527dee9575f4cf57deea0431. |
| Actual Predictable Change of Integrator for IBM-Observable Martingales | [LaTeX](ibm-stochastic-associativity/main.tex) · [PDF](ibm-stochastic-associativity/main.pdf) | Named claims aligned with verified Lean checkpoints1373–1374; original domains and OPEN physical-time obligations retained. Local two-pass compilation SUCCEEDED; all5 rendered pages inspected, notation legible, internal references resolved. Exact source/PDF freshness receipts accompany the files. Working exposition, not a novelty/submission/completed-IBM claim. | Revision1, October22,2026; mathematical baseline536c86647bd483eb547a264464dca7a2c0460026. |

Build/review evidence: [compiler status](ibm-stochastic-associativity/build-status.json),
[visual review](ibm-stochastic-associativity/visual-review.json),
[retained logs](ibm-stochastic-associativity/logs/).
Tracked artifacts are public on the user-designated GitHub repository. A future
substantive edit must update the PDF and
revision/status; mark PENDING if compilation/review is unfinished or the daily
budget is exhausted. Original ResearchSources files are not maintained drafts.
See [local compilation and review](README.md).
