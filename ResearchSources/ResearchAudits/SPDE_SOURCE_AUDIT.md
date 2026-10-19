# Fractional memory SPDE source inventory and adversarial audit

Recursive inventory: C:/Operator/spde contains exactly two TeX manuscripts and no PDF, Lean, Python, notebook, data, or other numerical source files. Hashes are in SPDE_MANIFEST_2026-10-12.json. No archive file was modified.

- `main(20261012-204518).tex` (71054 bytes): original fractional-memory SPDE, deterministic and forcing resolvents, whole-space Hilbert realization, Gaussian/jump operator claims, modal truncation.
- `paper_v_full_results_updated(5).tex` (65400 bytes): retrieval/retention application, numerical tables, parameter searches and decoder experiments described in prose. No executable experiments or data are present here. Reported performance is unverified and is not evidence for SPDE or operator identities.

Every manuscript claim below remains UNVERIFIED as a full source claim. A narrower proved result must be identified by exact Lean declaration separately; no successful build upgrades the whole manuscript.

## Source-to-theorem inventory

| Source location in main TeX | Claim | Status / obligation |
|---|---|---|
| 252, eq:caputo | Caputo derivative for 0<alpha<1 and 1<alpha<2 | UNVERIFIED; order>1 needs second initial datum, not merely X_0 |
| 275, 298 lem:ml_bounds | Mittag-Leffler series and uniform bounds | UNVERIFIED; stated endpoint alpha=2 invalidates decay bounds |
| 370 def:resolvent, 374 lem:resolvent_props | homogeneous S_t=E_alpha(-At^alpha) | UNVERIFIED; actual summability and Caputo identity needed |
| 384 def:resolvent_kernel | forcing Phi_t=t^(alpha-1)E_(alpha,alpha)(-At^alpha) | UNVERIFIED for nonzero A; distinguish from S_t |
| 398 thm:existence_trace | trace-class noise, L²(Omega;C_t L²_x) | UNVERIFIED; fixed-time integral estimate plausible for alpha>1/2, continuity proof needs repair |
| 453 thm:existence | cylindrical noise on L²(R) | UNVERIFIED / blocking defect: nonzero whole-space convolution operators are not Hilbert-Schmidt |
| 500 thm:continuity | pathwise continuity by factorization | UNVERIFIED; displayed factorization omits propagator and uses an unjustified resolvent composition |
| 537 thm:spectral; 554 cor:modewise; 558 cor:mode_variance | Fourier noise and scalar modes | UNVERIFIED; generalized white-noise Fourier coordinates are not individual L² variables; arbitrary Q is not white Fourier diagonal |
| 564 thm:spatial_reg | spatial smoothing | UNVERIFIED; Q-weighted HS criterion valid target, whole-space cylindrical criterion misidentified |
| 653 thm:temporal_reg | nearly 1/2 stochastic Holder exponent throughout range | UNVERIFIED / false in zero-rate one-mode model: variance at zero scales t^(2alpha-1) |
| 712 thm:energy | energy identity | UNVERIFIED; trace-class version needs ||Phi_s Q^(1/2)||_HS², not ||Phi_s||_HS² |
| 720 prop:dissipation; 732 thm:decay_det | energy contraction and spatial decay | UNVERIFIED; require separately proved ML estimates, not fractional product rule |
| 834 thm:stationary | stationary trace covariance | UNVERIFIED; conditional HS target is meaningful, Fourier multiplier trace formula on R is not |
| 900 thm:selfsimilar | exact variance scaling including arbitrary trace-class Q | UNVERIFIED / false without scale-compatible Q; proof discards Q |
| 993 def:energy_space; 1002 def:D_quijotic | integration-first derivative | UNVERIFIED / domain mismatch: deterministic bounded integral adjoint is first-chaos extraction, not full Malliavin derivative |
| 1028 thm:clark_ocone | all-L² formula using D_sF | UNVERIFIED as written; PRP for all centered L² differs from derivative formula on dom(D) |
| 1110ff def:defect, thm:defect_dichotomy | domain products and jump defect | UNVERIFIED; fg and field products need integrability/domain restrictions |
| 1150ff prop:defect_propagation | jump correction weights | UNVERIFIED; kernel envelope is not a proof identifying a product defect |
| 1224ff thm:eff_context; 1270ff thm:discretization | modal memory and impulse response | UNVERIFIED; finite Galerkin analogues preferable to point evaluation of generic Fourier L² classes |

## Blocking mathematical repairs

1. A nonzero multiplier M_m on L²(R) is not compact: choose a positive-measure set with |m|>=epsilon and infinitely many disjoint normalized indicators therein. Images are orthogonal and uniformly bounded below. Therefore it is not HS. Integrating |m|² over frequencies is a kernel-per-unit-volume calculation, not the HS norm of the whole-space convolution. Work on a compact spatial domain/discrete spectrum, use genuinely trace-class localized noise, or state local/weighted spatial results.
2. At alpha=2, E_2(-r)=cos(sqrt r), so C/(1+r) fails. E_(2,2)(-r)=sin(sqrt r)/sqrt r also violates that envelope. Restrict those decay lemmas to alpha<2. The positive Laplace-measure explanation for alpha>1 is incompatible with sign changes.
3. For alpha>1 specify X'_0 (often zero) in the Caputo problem. Mild-formula uniqueness is not automatically equivalence with a distributional Caputo equation.
4. Additional spatial smoothing does not remove the temporal threshold for a nonzero fixed noise mode. The leading response remains t^(alpha-1)/Gamma(alpha). At alpha<=1/2 even its scalar square integral diverges.
5. The zero-rate scalar response has variance t^(2alpha-1)/(Gamma(alpha)^2(2alpha-1)). At alpha in (1/2,1) this forbids arbitrary nearly-1/2 increment estimates at zero. Generic initial data in L² also have no uniform positive power modulus at zero for an unbounded generator.
6. The displayed factorization is invalid for a general fractional resolvent; even semigroup factorization must retain S(t-s) in the outer integral. Prove direct covariance/increment estimates instead.
7. Full Gaussian derivative, predictable adjoint and deterministic first-chaos adjoint must stay separate. The established rewrite gives exact bounded-kernel adjoint transport and projection identities only on the full derivative's actual domain.
8. E_alpha(-lambda t^alpha) and t^(alpha-1)E_(alpha,alpha)(-lambda t^alpha) have different long-time decay. For positive lambda and noninteger alpha<2 the latter is of order t^(-alpha-1), not the former t^(-alpha); the source alternates these kernels. Alpha=1 is exponential. Kernel estimates alone do not establish jump-product identities or unhedgeability.

## Retention manuscript

`paper_v_full_results_updated(5).tex`, thm:retention lines542ff and Appendix app:retention-proof lines1573ff: the strict inequality defines an open interval, whose real maximum does not exist; use supremum. The integer cutoff needs the strict-boundary correction when the crossing time is an integer. With fixed content ratio and lambda->0, lambda*tau^alpha tends a finite inverse-Mittag-Leffler argument, not automatically infinity. The scaling exponent can be correct while the displayed tail-derived asymptotic constant is unjustified without an additional regime. Numerical tables and decoder/model-performance claims remain outside this formalization.

## Pinned library reuse

Mathlib has Gamma, real powers, interval integrability and integration, actual Hilbert adjoints, Lp and Gaussian infrastructure. A recursive search found no two-parameter Mittag-Leffler special-function implementation; similarly named categorical Mittag-Leffler systems and the cotangent expansion are unrelated. Do not silently assume ML summability, resolvent identities, trace estimates or Caputo regularity.

Implementation priority: exact scalar temporal forcing threshold and variance; actual kernel-transform adjoints and finite-rank energy; then an independently constructed ML series/Caputo core and compact-domain spectral truncations. The full original SPDE is not yet proved.
