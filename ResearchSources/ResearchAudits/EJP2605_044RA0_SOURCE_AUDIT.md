# EJP2605-044RA0 source and theorem audit

Source: `C:\Operator\ibm\EJP2605-044RA0.pdf`, 24 pages, inspected 2026-10-12.
Title: *A Mollified Itô–Tanaka Formula for Iterated Brownian Motion and Its First-Chaos Dual Closure*, Ramiro Fontes.
SHA256: `5A91914A535AD19BDDF219D7A9AB9F8B5F20A52DD4EC6ED7333AA80B403182BE`.
The cover has placeholder volume/article/DOI and an empty acceptance date. No publication/acceptance status is inferred.
The original PDF is unchanged. Text extraction and rendered inspection copies are in `C:\Operator\ResearchAudits\pdf-extracts`.

## Source-to-theorem inventory

Every entry below is **UNVERIFIED** as a manuscript theorem: no exact Lean formalization is asserted by this inventory. Existing Gaussian results are prerequisites, not certification of these claims.

| Pages / source declarations | Claim and dependencies | Lean extraction priority |
|---|---|---|
| 3–5, setup, Lemmas 2.1–2.3 | Independent two-sided scenery and Brownian clock; convolution kernels; uniform O(epsilon) squared mollification error; derivative variances and covariance cancellation | First: actual Hilbert kernels, isonormal realization, bounded integral estimates |
| 5–6, Theorem 3.1, Definition 3.2, Corollary 3.3 | Brownian-time expectation solves fourth-order PDE with coefficient 1/8 and boundary source f''/(2 sqrt(2 pi t)) | Separate deterministic heat/half-normal calculation; not an ordinary Markov generator |
| 6–7, Proposition 3.4, Theorem 3.5 | Fixed-epsilon clock Itô–Tanaka identity and clock divergence identification | Requires local time, Tanaka, initially enlarged product filtration and genuine integrability |
| 7, Theorem 3.6, Remark 3.7 | Expectation convergence and reflection cancellation of boundary term | Uniform mollification error and independence; easier than pathwise limit |
| 8, Lemma 4.1 | Reflected local-time Sobolev regularity and failure of local H1 | Major local-time/occupation/quadratic-variation prerequisites |
| 8, Lemma 4.2 | Conditional first-scenery-chaos projection equals isonormal integral of averaged scenery derivative | Reuse genuine Gaussian adjoints, tensor/conditional projections and graph density |
| 8, Lemma 4.3 | Strong L2 approximation of non-H1 limit forces gradient norm blow-up | Reusable closed-graph/weak compactness argument; Fourier route also possible |
| 9–10, Theorem 4.4, Remarks 4.5–4.6 | First-chaos variance diverges under nonzero heat-averaged f'; cancellation leaves derivative of weighted local time | Must independently prove localized lower bound; structural assertion is not proof of no cancellation |
| 11–12, Definition 5.1, Remarks 5.2–5.3 | H1/H−1 test-dual pair and generalized conditional first-chaos pairing | High priority: bounded distributional derivative and pairing before any random correction |
| 12, Open problem 5.4 | Density of intrinsic observable pullback domain | Explicitly open; cannot define densely defined intrinsic adjoint by assumption |
| 13, Lemma 5.5, Remark 5.6 | Boundary covariance zero; no delta-prime boundary coefficient | Prove from even mollifier and actual Gaussian covariance |
| 13–14, Lemma 5.7 | Boundary-layer residual tends to zero in L2, O(sqrt(epsilon)) | Quantitative kernel estimates, local-time supremum moments, small epsilon qualification |
| 14, Assumption 5.8 | Whole-line zero-extended reflected local-time Sobolev moments | An explicit manuscript assumption, NOT a theorem available for import |
| 14–16, Theorem 5.9, Lemma 5.10, Proposition 5.11 | Qualitative H−1 interior closure; heat-time Lipschitz; conditional rate | Separate unconditional result from rate depending on 5.8 |
| 16–17, Theorem 5.12, Corollaries 5.13–5.14 | Boundary mollifier-to-delta convergence; full first-chaos dual closure and pairing convergence | Boundary distribution bookkeeping and Bochner L2, not just pathwise distributions |
| 17–19, Theorem 6.1, Lemma 6.2, Theorem 6.3 | Fixed-epsilon joint chaos expansion and pure-clock expectation blocks | Product Gaussian Hilbert decomposition; identify Pi00 as constants |
| 19, Open problem 6.4 | Random-functional boundary-layer limit | Open in paper; promising approximate-identity/local-time-continuity argument, not yet Lean |
| 19, Theorem 6.5, Remark 6.6 | Conditional first-chaos block projections inherit dual convergence | Bochner lift of orthogonal contractions; no claim all blocks are singular |
| 20–21, Proposition 6.7, Theorem 6.8, Proposition 6.9, Remark 6.10 | Six second-chaos contraction channels; boundary channel cancellation | Verify coefficients and symmetrization; fixed epsilon only |
| 22–23, Open problem 7.1 and directions | Global cross-sector dual limit, intrinsic density, higher source/observable operators | Not established; preserve as obligations |
| 23, Proposition A.1 | Failure of scalar Wick-square subtraction | Need quantitative non-cancellation argument, not merely an unchanged summand |
| 24, Proposition B.1 | Fourier-mode fourth-order expectation diagnostic | Correct half-normal normalization first |

## Independent mathematical concerns and minimal repairs

These are mathematical audit findings, **not Lean proofs** of the manuscript's theorems or their negations.

1. **Negative-time covariance sign (p.5, (2.7)).** The stated derivative of variance equals 1 for |r|>c epsilon. The variance formula later given in Lemma 5.7 instead yields sgn(r); Cov(U_r,V_r)=sgn(r)/2. Restrict (2.7) to r>c epsilon, which is what the clock applications use, or state the negative sign explicitly.
2. **Clock integrand paths (p.7, proof 3.5).** g'_epsilon(|Y_s|) sgn(Y_s) need not be continuous at zeros if g'_epsilon(0) is nonzero. Predictability/progressive measurability and L2 suffice; prove them for the product filtration with scenery initially known. It is not adapted to the clock-only filtration before conditioning on scenery.
3. **Unjustified scenery-domain explanation (p.12, F3).** For an independent random clock, the scenery derivative candidate of X_|Y_t| is the indicator kernel sigma_|Y_t|, whose squared Hilbert norm is |Y_t| and has finite expectation. The serious singularity is in the clock derivative, not automatically the scenery derivative. This does not settle intrinsic observable-core density, and nonmembership of particular observables does not prove failure of density.
4. **Joint divergence domain (p.11).** Dom(delta_X) direct-sum Dom(delta_Y) is a legitimate restricted divergence domain, but cannot silently be identified with the maximal adjoint of the joint gradient: cancellation between component divergences can enlarge the maximal domain. Reuse the already verified combined-coefficient domain discipline.
5. **A.s. L2 kernels vs Bochner L2 (Definition 5.1).** K(Y) in spatial L2 almost surely does not alone imply I1(K) in joint L2. Require E||K||²<infinity. Preserve this distinction throughout closure claims.
6. **Reflected local-time extension (Lemma 4.1).** The zero extension has a jump at zero when L(0+)>0; it is not globally 1/2-minus Hölder. Its fractional Sobolev regularity below 1/2 can still hold, but the cited Hölder argument must be localized or repaired at zero.
7. **Boundary cancellation must be inspected (5.11–5.13).** With standard normalization, L(0+)=2 L_t^0(Y). The distributional derivative of the zero extension C L contains C(0)L(0+) delta_0. Thus the explicit boundary term L_t^0 f'(x) delta_0 cancels the delta_0 contribution of -1/2 partial_w(C L). Keeping the decomposition is valid; claiming an uncancelled atom for the combined kernel requires correction. This does not eliminate the rough interior distribution or its L2 obstruction.
8. **Small-epsilon estimates.** Lemma 5.7's proof gives sqrt(epsilon)(C1+C2 epsilon), so its advertised uniform constant needs 0<epsilon<=1 (sufficient for convergence), or a displayed epsilon-dependent factor. Similar bounds in (6.5) need that qualification. The 5.12 Bochner rate constant also depends on t through E[(L_t^0)^2].
9. **Unchanged singular summand is not a non-cancellation proof (A.1).** Adding an epsilon-dependent divergent channel can in principle cancel another one. The no-stabilization conclusion needs an independent localized lower bound for the modified kernel.
10. **Individual chaos blocks (6.5).** Kernel convergence in H−1 does not prove the limit of every clock-chaos projection is outside L2; projection may regularize or vanish. State only the proved dual convergence and characterize individual L2 membership separately.
11. **Half-normal typo (p.24).** For phi_t the N(0,t) density, p_t=2 phi_t on positive s, not sqrt(2) phi_t. The displayed p_t and final PDE constants elsewhere are consistent with 2.
12. **Proof wording (Lemma 4.3).** Fourier L2 convergence does not directly give dominated pointwise convergence. Restricted multiplication by frequency on a bounded interval is a bounded L2 operator; use that to justify convergence of truncated energies.

## Integration-first implementation route

Keep the current queued campaigns in order. Do not identify the EJP manuscript with already proved IBM results.

1. Build a concrete Sobolev graph test space and its continuous dual; prove the actual weak derivative L2 -> H−1 bounded, with integration against actual test derivatives. Avoid a custom structure whose fields assert the sought calculus.
2. Prove continuous lifting/pairing on clock-valued Bochner L2 and deterministic contraction preservation. This rigorously explains why a divergence-first construction can select a weaker target without claiming an ordinary stochastic random variable exists.
3. Construct independent scenery/clock Gaussian sources, signed indicator kernels, their mollification and exact moment bounds. Reuse existing first-chaos isometries and actual closed derivatives.
4. Prove the conditional first-chaos projection theorem on polynomial tensors, extend by genuine graph approximation. Establish all domain statements explicitly.
5. Only after local time/Tanaka and moment infrastructure are proved, address fixed-epsilon correction, localized blow-up, boundary cancellation and H−1 closure.
6. Treat F1–F3 as open. First pursue the boundary-layer approximate-identity statement rather than inventing a global dual topology or presupposing intrinsic density.

The operator-first contribution must be judged by proved domain/closure/transfer results, not by changing names for classical Malliavin objects. A useful extension would explicitly distinguish a densely defined observable derivative, a nondense closed pullback relation, and a distribution-valued first-chaos limit.
