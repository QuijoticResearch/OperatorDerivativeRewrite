# A(2): arithmetic and operator method transfer audit

Checkpoint 1272; October 21, 2026. The active campaign remains A(2).
The hard stopping date and final multichannel gate remain unchanged.

## Exact transfer now verified

Write `H_t = RiemannEvenFlow.flow 1 t` in the existing normalization.
`RiemannQuadraticArithmeticHeat.zero_time_strip` assumes the actual statement
`forall w : Complex, theta < w.re -> riemannZeta w != 0` and proves that every
zero of `H_0` has `|Im z| <= 2*theta-1`. Its proof uses the existing completed-Xi
coordinate `s=1/2+i*z/2`, pole-cancellation/imaginary-axis positivity, and actual
conjugation symmetry. No new identification of an entire function is assumed.

`heat_strip` then proves, for every real `t>=0` and actual zero of `H_t`,

```
(Im z)^2 <= max ((2*theta-1)^2 - 2*t, 0).
```

`real_after_wait` gives all zeros real at every
`t >= (2*theta-1)^2/2`. These theorems allow any real `theta` under the explicit
arithmetic hypothesis; they do not assert that this hypothesis holds for any
particular parameter. The meaningful classical range starts at `theta=1/2`.
In particular, a negative proposed strip width is not silently replaced by its
absolute value in the zero-time theorem.

| Arithmetic boundary | Resulting all-real waiting time | Input status |
| --- | --- | --- |
| `1` | `1/2` | Classical input already discharged in production 1270 |
| `11/12` | `25/72` | Conditional instance tested; weaker than the audited `7/8` input |
| `7/8` | `9/32` | Actual upstream input and actual heat consequence independently checked in isolation, 1271 |
| `3/4` | `1/8` | Conditional test only; no such arithmetic input established here |
| `1/2` | `0` | Strong arithmetic premise remains unproved here |

`critical_half_plane_real_forward` retains the full `Re(s)>1/2` premise.
`asymptotic_half_planes_real_forward` requires an independent zero-free assertion
for **every** half-plane `Re(s)>1/2+epsilon`, `epsilon>0`. It proves the endpoint
premise by choosing a positive epsilon below each given real-part gap. This is
a quantifier argument, not a Hurwitz or flow-parameter limit. It does not obtain
arbitrarily narrow strips by iterating the one known `7/8` theorem.

The arbitrary-time version remains `RiemannQuadraticStripEvolution` (1271): an
actual global strip of width `b` at any real starting time contracts with
squared width `max(b^2-2*s,0)` after elapsed time `s>=0`. Once-real-always-real
has no nonnegative starting-time restriction. Actual Xi still lies outside the
bounded factorial-jet space; the finite-polynomial/operator/actual-Gaussian
approximation and explicit entire nonzero limit domains are essential.

## Concrete limitations checked in Lean

`polynomial_strip_sharpness` uses the real polynomial `P=X^2+9/16`. All its
initial complex roots satisfy `|Im|<=3/4`. The actual existing polynomial heat
operator `transport 2 (-1/4)` nevertheless has the nonreal root `i/4`. This
attains the squared contraction width `9/16-2*(1/4)=1/16`. It refutes an
all-real-at-`1/4` inference from these strip data for the general polynomial
class. It is **not** an actual Xi counterexample, and makes no claim against a
stronger Xi theorem using additional arithmetic information.

`real_axis_exclusion_not_half_plane` constructs the entire, conjugation-
symmetric polynomial function `f(z)=(z-1)^2+1`. It is nonzero at every real
argument but vanishes at `1+i`, to the right of `7/8`. Thus exclusion on the
real axis does not by itself imply complex half-plane nonvanishing, even for
this entire symmetric class. The witness is not a Dirichlet L-function.

## Pinned external sources and scope of review

The OpenAI source revision is
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`, not an assertion about the latest
repository state. Exact source SHA256s and source URLs are preserved in
`STARDUST_A2_OPENAI_SOURCE_INVENTORY.json`,
`STARDUST_A2_UPSTREAM_IMPORT_INVENTORY.json`, and
`STARDUST_A2_PATCHED_SUPPORT_INVENTORY.json`.

This checkpoint selectively read the quasi-Riemann paper's abstract,
introduction and proof overview (source lines 35–277), opening of the final
seven-eighths argument (15495–15599), and final closure (16426–16473).
The formalization scope note `lean/docs/003.md` was read in full. The external
assembly `OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional`
and follow-up `SiegelZeros/Main.lean`, `SiegelZeros/Conclusions/Theorem.lean`
and its release README were read. This is **selective mathematical method
review**, not a claim to have human-audited every proof in the 16,677-line paper.

The independently kernel-replayed targets remain exactly
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` and
`OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re`.
Their 7059-job replay and exact transitive axiom audit are recorded in
`STARDUST_A2_UPSTREAM_VERIFICATION.json`. The actual heat integration is in
`STARDUST_A2_HEAT_UPSTREAM_INTEGRATION.json`. Only the isolated child process
adds the existing OAI build artifacts to `LEAN_PATH`. Production dependencies,
versions and trust settings remain unchanged. Neither the separate Hecke
entrypoint nor the follow-up entrypoint is certified by those two target audits.

The paper compares reflected completed cubic-theta sums with Poisson/Mellin
representations containing reciprocal Hecke L-functions. Its first `11/12`
stage uses balanced scales and a sextic row count. The `7/8` stage uses local
prime compensation, asymmetric scales, and matched inverse/plain moment
estimates. Fixed numerical parameter choices and positive exponent margins
enter the inspected assembly. Replacing `7/8` by another parameter requires
new estimates and their hypotheses; no such replacement follows from the
generic heat theorem. The reviewed conclusion is not a contraction theorem
for Stardust's actual positive theta kernel.

Stardust's Gaussian integration, finite polynomial heat, divisor products,
zero-strip closure and zero dynamics supply the rigorous downstream transfer.
They do not supply the paper's arithmetic characters, conductor-uniform moment
inequalities, reciprocal-L continuation or prime-compensation estimates.
Likewise, the paper's auxiliary Gaussian factor is not automatically the
probability law in Stardust's actual imaginary-Gaussian heat identity.
No automorphic identity with the quartic or general even-order flow is asserted.

The October 1 follow-up's inspected theorem concerns **real** zeros of
primitive nonprincipal real Dirichlet characters and a logarithmic conductor
gap. It is not a stronger bound on all complex zeros of zeta. Its conclusion
calls a local isolated Bezout selection theorem; the full separate dependency
proof remains outside the two audited entrypoints. For A(2), transferring its
stated real-zero conclusion alone would leave the complex-zero problem open.
The polynomial counterexample above tests that logical distinction; it neither
verifies nor refutes the follow-up's arithmetic proof.

## Remaining mathematical work

The actual normalization, Gaussian/operator bridge, global strip transfer,
arbitrary starting times and once-real preservation are now verified. Exact
Newman threshold, zero-time reality/RH, and a stronger Xi-specific arithmetic
estimate remain open. No novelty or improved numerical-record claim is made.
An additional useful next question is whether existing actual parameter-
continuity and zero-limit machinery proves closedness of the set of all-real
times, including its boundary, without assuming an attained finite threshold.
That requires an exact reuse/domain audit first. It is not yet proved here.
The A(2) campaign has not been declared stopped; the final multichannel campaign
remains gated by an explicit audited stopping checkpoint.
