# A(2) verified stopping audit

Checkpoint 1276, October 21, 2026. Mathematical baseline:
`ae2b484e9f58f194d006a9af4120e4f93e338cfc` (checkpoint 1275).
This is a stopping audit, not a new theorem or a claim that all classical
quadratic-flow questions have been solved. The transition to the final
multichannel campaign requires this checkpoint's full verification, explicit
Git commit, exact-commit receipt and verified PRIVATE backup first.

## Actual object and proved conclusions

Throughout, `H_t(z) = RiemannEvenFlow.flow 1 t z`, in Stardust's existing
normalization. At time zero this is `entireXi(1/2+I*z/2)/8`, throughout the
complex plane. The existing pole-removal and imaginary-axis nonvanishing
arguments are retained. No unspecified external nonzero-time convention is
identified with this parameter.

`RiemannQuadraticFiniteThreshold.threshold` is the real infimum Lambda of the
ACTUAL all-real time set. There is no assumed bounded-below premise in the
final results:

- `real_times_bddBelow` proves that premise independently.
- `real_times_eq_Ici` proves the set is exactly `[Lambda,infinity)`.
- `real_zeros_iff t` proves, for every real t, that ALL complex zeros of H_t
  are real if and only if Lambda <= t. The endpoint is included.
- `nonreal_zeros_iff t` proves that an actual nonreal zero exists if and only
  if t < Lambda. This includes actual negative-time witnesses, with no
  numerical zero location claimed.
- `threshold_le_half` proves Lambda <= 1/2 in production.
- `threshold_le_seven_eighths` proves Lambda <= 9/32 under the explicit
  actual-zeta nonvanishing hypothesis on Re(s)>7/8. The isolated adapter
  actually supplies the independently replayed pinned upstream theorem;
  its unconditional integrated bound and attained-threshold criterion are
  recorded in `STARDUST_A2_FINITE_THRESHOLD_UPSTREAM_INTEGRATION.json`.

These are formalizations of classical threshold properties and their known
arithmetic consequence, not new numerical records. Neither inequality proves
the sign of Lambda. `zero_time_reality_iff` states exactly H_0 all-real iff
Lambda <= 0; it proves neither side separately. No RH progress is claimed.

## Theorem-level reuse and domain audit

| Machinery | Verified use for the actual quadratic flow | Essential boundary |
| --- | --- | --- |
| Xi bridge | `RiemannQuadraticXiTransfer.real_order_zero_time`, `zero_iff_completed`, actual zeta half-plane transfer | Zero-time identity, explicit pole exclusions where required; no external nonzero-time clock imported |
| Operator derivatives and Gaussian transport | `RiemannQuadraticPolynomialHeat`, `RiemannQuadraticOperatorApproximation`, `RiemannQuadraticUniformHeat`, `RiemannQuadraticGaussian` | Exact finite polynomial calculus and actual entire limits; the infinite Xi vector is outside the bounded factorial-jet domain (1249) |
| Zero dynamics and global estimates | `RiemannQuadraticRootMotion`, polynomial collision/cluster machinery, `RiemannQuadraticGlobalStrip.flow_zero_strip` | Topmost-root comparisons are not claims that every root's height decreases; multiplicities and collisions enter the finite-polynomial proof |
| Arbitrary-time strip evolution | `RiemannQuadraticStripEvolution.strip_from_time`, `once_real_always_real` | Given an actual global initial strip at any real time, squared width is at most max(b^2-2s,0), s>=0 |
| Arithmetic transfer | `RiemannQuadraticArithmeticHeat.zero_time_strip`, `heat_strip`, `real_after_wait` | Actual zeta half-plane hypothesis is explicit; no iteration of a fixed 7/8 theorem toward 1/2 |
| Fourier moments and higher-order saddle work | Existing actual integral/moment bounds; `RiemannEvenRealSaddle.weighted_tendsto_zero 2 T` supplies decay of exp(T*x^4)*kernel(x) | Common actual density decay is reused, not a relation between A(4) and A(2) thresholds; cosine approximation alone does not give global zeros |
| Closedness and zero limits | `RiemannEvenRealityClosed.isClosed_realTimes`, for every natural order including zero | Actual pointwise time continuity plus polynomial-divisor vertical modulus bounds and a nonzero analytic limit; no general pointwise Hurwitz theorem asserted |
| Finite lower bound | `NewmanFourPointBound.actual_flow_four_point`, `RiemannQuadraticDensitySmoothing`, `RiemannQuadraticDensityHeat`, `RiemannQuadraticFiniteThreshold.not_all_real_times` | All-real premise, nonzero origin, actual Gaussian integrability and positive log limits are proved/used explicitly |
| Local collision models | `RiemannQuadraticAllOrders`, `RiemannQuadraticHermite`, `RiemannQuadraticZeroTransfer.actual_unique_simple_near_model_root` | Forward time t+h^2 and finite multiplicity hypotheses; not a proof of an actual threshold collision or a backward nonreal branch |

The lower-bound connection is an actual Gaussian-integral identity. For
variance v>0, s=1/(2v), N=1/sqrt(2*pi*v), and
rho(u)=kernel(abs(u)), `gaussian_heat_identity` proves

```
complex(E_gaussian(mean x, variance v)[rho])
  = complex(2*N*exp(-s*x^2))*H_(-s)(I*2*s*x).
```

It proves L1 integrability before rewriting the integral. At variance zero
the Gaussian is Dirac while the ordinary density is zero; the existing
verified counterexample excludes that extension. For smoothing by x+epsilon*Y,
Y of variance 2, the clock is -1/(4*epsilon^2), epsilon != 0. Five positive
logarithmic pointwise limits transfer a four-point inequality to rho. That
inequality would force a quartic exponential lower bound, contradicting the
existing actual density decay for every real T. Hence some actual time has
a nonreal zero. Closedness and upward preservation then give finite attainment.
No full measure classification, diagonal degree limit, uniform bound on all
pre-threshold zeros, or unproved derivative convergence is hidden here.

## Explicit counterexamples and stopping obstructions

`RiemannQuadraticArithmeticHeat.polynomial_strip_sharpness` uses
P=X^2+9/16 and the actual finite heat operator at elapsed time 1/4. Its root
I/4 saturates the surviving squared strip width 1/16. Thus those strip data
alone do not imply all-real zeros at time 1/4 for the general polynomial
class. It is not an actual Xi counterexample.

`real_axis_exclusion_not_half_plane` uses (z-1)^2+1: it has no real zeros but
has the zero 1+I. Even entire conjugation symmetry does not upgrade real-axis
exclusion to complex half-plane exclusion. This does not verify or refute an
arithmetic theorem about Dirichlet L-functions.

The root-motion interior-root counterexamples, the nonzero-origin requirement
in the four-point product bound, the zero-variance counterexample, and the
bounded factorial-domain obstruction remain in force. They prevent several
shortcuts, not stronger theorems with additional correct hypotheses.

## Pinned OpenAI paper: mathematical transfer and scope

Revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a` is the audited snapshot,
not a claim about the current upstream head. The paper, formalization notes
and follow-up source hashes/URLs are preserved in the existing inventories.
The paper SHA256 is
`42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3`.

The stopping review read all 64 theorem/proposition/lemma/corollary statement
blocks across the 16,677-line paper, and selectively read proofs, including
the complete common-signal continuation argument (source 363-556) and final
order-of-choices/closure (16186-16473). The statement index and exact selected
proof ranges are recorded in `STARDUST_A2_PAPER_METHOD_REVIEW.json`. This
extends the earlier introduction/final-assembly review. It is still NOT a
human verification of every intervening proof. The kernel replay of the two
exact targets is separate, stronger evidence for those targets and weaker
evidence for any uninspected separate entrypoint.

The primitive-Hecke family over Q(sqrt(-3)), completed cubic-theta reflection,
sextic sieves, masked Poisson, fixed-ray prime compensation, inverse/plain
moments, and conductor-dependent row bins are arithmetic input. Stardust's
positive theta density and Gaussian transport do not establish these estimates.
The paper's lognormal auxiliary test and exp((s-5/6)^2) Mellin factor are not
automatically the law in the actual Gaussian/heat identity above. Common
profiles, zero extensions on nonunits, coefficient independence from rows,
and a single cumulative height allowance are explicit constraints, not
optional generic Hilbert-space replacements.

The continuation proposition takes C(s)=s+c, sigma0>1/2, a hypothetical
family supremum beta*>sigma0, and target-independent positive exponents
0<omega<beta*-sigma0 and sigma>0. Constants, finite Euler exclusions and lower
thresholds may depend on the target. The Mellin signal then has saving
epsilon*=min(beta*-sigma0-omega,sigma)>0 shared across the family. Its
holomorphic numerator is uniformly within 1/2 of 1, allowing division.
This is not merely a real-axis zero detector. The late height lemma fixes
all internal finite seminorm/height orders before selecting the target's
height exponent, then the external tail order; increasing that tail order
must not change those earlier polynomial degrees.

There is a concrete boundary to direct reuse. `prop:probe-low` (8564-8576)
has exponent 3/16+epsilon, and the final C(s)=s-11/16 gives

```
C(beta*) - (3/16 + epsilon) = beta* - 7/8 - epsilon.
```

For beta*<=7/8 this is strictly negative, so the SAME low estimate cannot
supply the required positive low-side saving. Multiplying both signal and
probe by any common power of Z shifts both exponents equally and leaves
this deficit unchanged. This elementary algebra is a written audit conclusion,
not a new Lean declaration and not an impossibility theorem for improved
arithmetic estimates. A new bound/geometry and its high-side hypotheses are
needed. The paper's local-product region, moment domains and final positive
capacity margins also cannot silently be extended outside their stated ranges.

Two uniformity questions must remain distinct. A fixed boundary continuation
argument needs a common positive saving across characters. By contrast, if
actual zero-free half-planes Re(s)>1/2+epsilon were independently proved for
EVERY epsilon>0, no uniformity of their constants as epsilon decreases would
be required to exclude each zero with Re(s)>1/2. This quantifier implication
is already Lean-verified by `asymptotic_half_planes_real_forward`. Degenerating
constants alone do not refute it; the missing input is those actual statements.

The independently replayed targets are exactly
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` and
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`.
The corrected configured replay covers 7,059 jobs, with only propext,
Classical.choice and Quot.sound in their transitive audits. Required published
support patches, raw/effective hashes and the setup failure of the earlier
unpatched run remain documented. No production import/toolchain/trust change
was made. The isolated heat/finite-threshold adapters use actual declarations.
Neither the separate Hecke entrypoint nor the October 1 follow-up entrypoint
was independently replayed here. The inspected follow-up concerns real zeros
of primitive nonprincipal real Dirichlet characters with a logarithmic conductor
gap; it is not a stronger complex zeta half-plane theorem. Full separate
follow-up proof review remains outside this frozen campaign's certification.

## Remaining questions and freeze decision

OPEN: Lambda's exact value and sign; actual H_0 all-real/RH; a stronger
Xi-specific arithmetic estimate; global compactness of pre-threshold nonreal
zeros; an actual multiple zero/collision at Lambda; endpoint/interior simplicity;
and independent verification of external targets beyond the two named above.
No implication from quartic/global integer re-entry, a real-order limit, a
generic entire-function counterexample, or forward local splitting closes
these questions. Those would require substantive new input, not a missing
coercion or an already-established premise in the current source chain.

The saved A(2) objectives were reuse, a small number of concrete applicable
theorems/obstructions, and a precise arithmetic/operator comparison. The
actual global strip, arbitrary-time preservation, finite attained threshold
and audited 9/32 integration meet that focused stopping objective. Freeze
A(2) after this checkpoint's exact PRIVATE gate. Preserve all unresolved
claims and prior proofs. Then begin the FINAL multichannel pseudoprocess
attempt from the existing signed calculus, adapted integral and finite-grid
reconstruction: all three biharmonic channels including centered cubic,
then the general p-1 channels and completed analytic domain. One-/two-channel
obstructions are not full-channel impossibility. October 31 is the hard stop;
freeze and stop then, with no new campaign.
