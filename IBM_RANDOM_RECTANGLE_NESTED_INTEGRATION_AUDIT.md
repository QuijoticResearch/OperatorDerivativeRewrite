# Actual random-rectangle pull-out and full L2 nested integration — checkpoint1372

The1371 common predictable multiplier is now identified with actual stochastic
steps on random rectangles. Finite predictable integrals against every completed
terminal channel have genuine completed inputs. Their isometric extension covers
ALL of the output channel's ORIGINAL random predictable L2 energy space, and its
actual output is the preexisting stochastic integral. No new process law,
filtration, energy measure or stochastic integral replaces the existing objects.

## Actual pull-out on every original channel input

`Foundation/IBMPredictableRectanglePullout.lean` reuses MultiplierCore's existing
bounded L2 multiplier for the sample-event coefficient; sampleMask is proved AE
equal to literal sample restriction. An event A is measurable in the ORIGINAL
raw natural past at s. It is not assumed measurable at earlier times or freely
anticipative. Future and rectangle multipliers remain measurable for the
ORIGINAL raw predictable sigma algebra on time×sample.

For each original dictionary cell (a,b]×B, raise its left endpoint to max(a,s)
and its right endpoint to max(max(a,s),b). The latter handles the empty tail
when b<=s. Transport B's raw-past measurability to the new left endpoint, and
intersect with A, now also measurable there. Prove the exact original process
identities and actual step-integral AE identities, including boundary/empty cases.

The literal tail process is H-C_s H on dictionary cells, and1370's cutoff
intertwining identifies its stochastic output as Y-P_s Y. Actual multiplication
by A then gives the future-event pull-out. Original dictionary density and
continuity extend the result to EVERY H in the ORIGINAL full L2(mu_F):

`I_F[1_((s,infinity)×A) H] = 1_A (I_F H-P_s I_F H)`.

For s<=t, subtract the two future multipliers using raw filtration monotonicity
for A at t. This proves the ACTUAL random-rectangle identity

`I_F[1_((s,t]×A) H] = 1_A (P_t-P_s) I_F H`.

The right side is a bounded linear output operator with an explicit AE formula,
and is PROVED equal to the EXISTING germ-predictable stochastic stepClass with
the ORIGINAL event coefficient. This is actual stochastic identification, not
merely a matching expectation, norm or formal covariance equation.

## All completed channel families and genuine finite stochastic integrals

`Foundation/IBMCompletedStochasticAssociativity.lean` extends the rectangle
identity by the existing dense raw embedding to EVERY family F and EVERY z in
its genuine joint-energy completion. With Y=J_F z, the actual stochastic output
of1371's M_rectangle z is exactly 1_A(P_t-P_s)Y, including the AE sample formula.
No arbitrary-family coordinate representation is required.

For an arbitrary OLD finite predictable presentation l, sum its original
rectangle operators with its actual coefficients. Evaluation at z gives the
linear finiteInput(z,l). Prove

`J_F finiteInput(z,l) = oldIntegralLinear(Y,l)`.

The right side is the EXISTING actual finite stochastic integral against the
single terminal-observable martingale P_t Y. It is not a new integral assigned
the desired value. The actual stochastic isometry and OLD dictionary norm give

`norm(finiteInput(z,l)) = norm(dictionary(Y,l))`.

Thus zero/equal original Y-energy presentations collapse correctly in the
completed input. This is a stronger calibration than componentwise bounds or
an algebraic product law alone.

## Full original L2 closure and exact topology

The OLD dictionary is dense in the ENTIRE original random predictable L2(mu_Y).
Pinned LinearMap.extendOfIsometry constructs

`nestedIntegral(z) : L2(mu_Y) -> isometrically Completed(F)`.

It agrees with finiteInput on every original dictionary input. Continuity and
that discharged density prove for EVERY original H in L2(mu_Y)

`J_F nestedIntegral(z,H) = OLD I_Y H`.

The lift is norm preserving and unique among isometries with those finite
agreements. Original finite dictionary approximations converging to H in its
original L2(mu_Y) norm converge in completed F-input norm to nestedIntegral(z,H),
and their ACTUAL stochastic outputs converge in original joint-source L2 to
I_Y H. The independent tests construct those approximations from the existing
existence theorem, rather than leaving existence conditional.

Consequently the actual range of EVERY completed family J_F is stable under
ALL original stochastic integrals I_Y H whenever Y is in that range. This is
an exact range-closure theorem, with the Y-membership premise discharged by z
in the main construction. The full L2 domain includes unbounded integrands
when they genuinely belong to L2(mu_Y); it is not restricted to finite grids,
bounded functions, finite chaos or a common auxiliary measure.

The dependent domain is L2(mu_Y). This does NOT silently prove that products
H*H_i lie in each original component L2(mu_Fi), or extend1371's pointwise-bounded
multiplier action to arbitrary unbounded functions. The lift is constructed
from actual finite operators and genuine completion, retaining exact domains.

## Precise remaining obligations

A general1371 bounded multiplier M_g is identified here on rectangle generators
and finite linear combinations. Equality with nestedIntegral(z, class(g)) for
EVERY bounded raw-predictable g still needs an appropriate bounded/measure
convergence or monotone-class argument. Uniform convergence in operator norm
alone does not supply finite-rectangle uniform approximation of every measurable
g. Do not claim that missing identification has been established.

Physical-time Itô/Tanaka for the uncorrected actual IBM path, conditional temporal
Malliavin-gradient Clark–Ocone, sample-path brackets/regularity and full intrinsic
calculus remain open beyond earlier exact scopes. Terminal martingales P_t Y
are actual martingales; the uncorrected IBM path remains non-martingale in ANY
filtration, as explicitly tested. IBM remains ACTIVE; no queued campaign begins.

Fresh full root build, complete transitive safe Foundation axiom audit, ALL38
unabridged new public types,12 printed definitions,403 final source/proof lines,
eight actual-object tests, prior source/config identity,113 immutable manuscript
path/hashes, ledger, Git receipt and verified PRIVATE main/research refs are the
closure gates. Exact timings, failed attempts and diagnostics are recorded in
the verification JSON. Default proof resources, trust and toolchain unchanged;
style warnings retained without suppression.
