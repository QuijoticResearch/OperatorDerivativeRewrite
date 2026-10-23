# Actual predictable time stopping and causal IBM reconstruction — checkpoint1370

The original predictable stochastic integral now intertwines literal time
truncation with the existing observed right-germ projection. The fixed-family
completed integral has a stopping operator identified with genuinely stopped
original coordinates, not only an abstract transported projection. This gives
causal conditional-observable reconstruction for every intrinsic L2 terminal
observable, and point-time reconstruction of the actual IBM process values.
It does not prove a temporal-gradient Clark–Ocone formula or physical-time Itô.

## Original integrands and actual processes

`Foundation/IBMPredictableTimeCutoff.lean` works in the ORIGINAL random predictable
L2(mu_F), for every existing channel F. The actual raw predictable sigma algebra,
energy measure, channel and original integral are unchanged. Define timeSet(t)
as the literal rectangle (0,t]×original sample space and construct a bounded
linear cutoff C_t whose actual representative equals 1_timeSet(t) H mu_F-AE.
The norm is contractive, C_s C_t=C_min(s,t), and C_0=0.

At a genuine elementary rectangle (a,b]×A, the stopped right endpoint is
max(a,min(b,t)). Its event A and coefficient remain measurable in the original
raw past at a, including the empty-interval cases t<=a. The ORIGINAL weighted
terminal-channel step identity and the tower law prove the exact stochastic
projection formula. Finite presentations are transformed linearly through those
stopped indices. Density of the OLD finite dictionary and continuity then give

`I_F(C_t H) = P_t(I_F H)` for EVERY ORIGINAL predictable L2 input H.

Here P_t is orthogonal projection onto the existing rightPast(t), equivalent to
conditional expectation in the existing germ filtration. No new filtration,
process law, independence, predictable measure or integral is postulated.
The original chosen L2 representative of each output is germ measurable;
t -> I_F(C_t H) is an actual martingale for the original joint source law.
C_t H is right continuous in its ORIGINAL integrand L2 norm, C_n H -> H for
natural-number horizons n -> infinity, and the exact increment-energy identity
is verified. These are strong L2 statements, not a claim of cadlag sample paths.

## Completed stopping and literal coordinates

`Foundation/IBMCompletedTimeCutoff.lean` uses the preexisting fixed countable
channel family, genuine joint-energy null quotient/completion J, and the old
initial-germ decomposition. Define S_t=J* P_t J. Prove that P_t Jz is intrinsic
and still orthogonal to the WHOLE original initial germ;1369 recovery therefore
proves J S_t z=P_t Jz. Contractivity, S_s S_t=S_min(s,t), S_0=0, right continuity
in the completed Hilbert norm and S_n z -> z follow from original projections
and actual stochastic isometry. No triviality of the initial germ is assumed.

This definition alone would not identify actual time stopping. For EVERY fixed
completed input z, take its1369 original coordinates H_i(z) and truncate EACH
in its OWN original L2(mu_(F_i)). The genuinely stopped integral series has
unconditional stochastic L2 HasSum J S_t z. The FULL signed joint Gram-tail
criterion then constructs its completed quotient HasSum; actual J injectivity
identifies the resulting input as EXACTLY S_t z. Stopping also agrees with
literal cutoff on EVERY embedded ORIGINAL single-channel input.

For arbitrary finite channel families and arbitrary ORIGINAL random integrands,
prove that the actual sum of stopped integrals equals P_t of the actual sum.
Consequently its FULL signed joint energy, including every cross term, is at
most its original joint energy. Exact cancellations survive stopping. There is
no false diagonal-only replacement of general signed covariance energy.
A completed stopping operator for EVERY arbitrary channel family is not newly
constructed here; finite-family contraction and the fixed-family construction
are the exact scope.

## Conditional observable and actual point reconstruction

For EVERY intrinsic terminal f, let z=J*f, the UNIQUE completed integrand already
identified by1369 native full-adjoint-graph pairings. Then the ACTUAL stochastic
integrals of C_t H_i(z) have unconditional L2 sum

`P_t f - P_0 f`.

This retains prediction onto the WHOLE initial germ. For f equal to the ACTUAL
IBM value at T and t=T, original past membership and the proved zero initial
prediction reduce the sum to that ACTUAL IBM value, including T=0.
The positive-time ordinary joint derivative obstruction remains true.

The integrand z depends on the terminal observable. In particular the theorem
for f=IBM_T uses a terminal-dependent input; it does NOT represent the entire
uncorrected IBM path by one fixed martingale integrand. The prior theorem that
actual IBM is not a martingale in ANY filtration is preserved and explicitly
combined with the new stopped-integral martingales in independent tests.
No contradiction, changed process, or forced semimartingale claim is introduced.

## Exact remaining obligations and verification

A conditional temporal-gradient identification of these coordinates, physical-
time Itô/Tanaka identities for actual IBM, brackets/path regularity and the full
intrinsic stochastic calculus remain open beyond earlier exact scopes.
Do not call conditional-observable integral reconstruction a proved Malliavin
Clark–Ocone formula. Uniform-in-time or joint terminal-parameter convergence,
cadlag modifications and a common terminal-independent IBM integrand are not
established here. Next investigate a substantive intrinsic formula/closure
connection using this actual stopping rather than extend static notation.
IBM remains ACTIVE; no queued campaign begins.

All40 unabridged new public types,12 printed definitions,385 final source/proof
lines, fresh full root build, COMPLETE transitive safe Foundation axiom audit,
eight independent actual-object tests, prior-source/configuration integrity and
113 immutable archive path/hashes are required. The verification JSON records
actual terminal timings, logs, development diagnostics and precise scope.
All builds and checks serialized. No added resources, axiom, toolchain change,
source deletion or suppressed check. Long-line style warnings are
retained rather than disabled; they do not weaken the mathematical audit.
Two finite-family statements also retain ordinary classically available
DecidableEq index parameters; the unusedDecidableInType linter warnings are
recorded and not suppressed. They introduce no analytic family restriction.
