# Bounded predictable multiplication on actual IBM joint energy — checkpoint1371

A genuine bounded multiplier action is constructed on the EXISTING signed-energy
null quotient and its Hilbert completion, for EVERY family of original IBM
channels. The action agrees with literal multiplication in each original random
predictable L2 space and with the actual stochastic integrals of those products.
The joint-energy bound preserves cancellations; componentwise norm bounds alone
would not justify this construction.

## Exact domains and signed pairing

`Foundation/IBMJointPredictableMultiplier.lean` uses the ORIGINAL raw predictable
sigma algebra on time×sample Space. BoundedPredictable records an ACTUAL real
measurable function g, a nonnegative B, and the pointwise bound norm(g(p))<=B.
This covers bounded predictable functions on that original sigma algebra;
there is no deterministic, grid, channel-independence or Gaussian-increment
restriction. A merely AE-bounded function in some unrelated/common measure is
not silently admitted. No new probability law, predictable measure or stochastic
integral is created. The package stores a bound for proof purposes; the induced
operator is proved independent of the choice of bound whenever the functions
agree pointwise.

For every old channel F and EVERY H in its ORIGINAL full random L2(mu_F), actual
multiplication gH is MemLp2 and its L2 class defines a bounded linear map. Its
representative is proved mu_F-AE equal to the literal product. No separate
common L2 domain replaces the original channel domains.

Let c(p)=sqrt(B²-g(p)²). Its real square root, measurability, bound and identity
g(p)²+c(p)²=B² are proved, including B=0 and points where equality holds. Using
1367's ACTUAL signed cross-covariance identity and the independently verified
absolute continuity of its variation with respect to EACH original channel
measure, prove

`<I_F(gH), I_G(gK)> + <I_F(cH), I_G(cK)> = B² <I_F(H), I_G(K)>`.

The separate original AE representatives are transported to the actual signed
variation measure; product integrability and signed integral linearity are
proved/reused, not assumed. Summing every cross term proves the full identity

`E(gH) + E(cH) = B² E(H)`.

E is the EXISTING full signed joint Gram energy, equal to the actual stochastic
sum's squared norm. Nonnegativity of E(cH) therefore gives E(gH)<=B²E(H) and
the corresponding actual stochastic norm bound. This does not assert positivity
of each cross signed measure or remove any cancellation counterexample.

## Actual null quotient and completion

`Foundation/IBMCompletedPredictableMultiplier.lean` defines componentwise gH
on the existing dependent direct sum. The actual modified stochastic sum agrees
with the sum of the ORIGINAL integrals I_Fi(gH_i). The full bound proves exact
preservation of the old rawIntegral kernel, so the map descends to the ACTUAL
null quotient by a proved mapQ compatibility condition.

The quotient norm bound makes this a continuous linear operator. Pinned
ContinuousLinearMap.completion then constructs its operator M_g on the genuine
Hilbert completion. M_g agrees with every original embedded single input and
all finite raw inputs, satisfies norm(M_g)<=B, and is UNIQUE among continuous
linear maps with those original agreements. No arbitrary algebraic action on
an unrelated Hilbert model substitutes for original stochastic integration.

Constants, addition and multiplication agree with the corresponding operator
operations: M_a=a id, M_(g+h)=M_g+M_h, M_(gh)=M_g M_h, and the operators commute.
Predictable indicator operators are idempotent. The literal indicator of (0,t]
is proved equal to the1370 old integrand cutoff on EVERY original channel input;
its fixed-family completed operator is EXACTLY the previously verified S_t.
Thus the new action connects to actual time stopping rather than only sharing
an abstract projection law.

Every original coordinate series already converging in the JOINT-energy
completion can be multiplied by g: the result has unconditional HasSum in that
completion to M_g z and in ACTUAL stochastic L2 to J M_g z. In particular EVERY
fixed-family completed input has such a genuine multiplied canonical series.
No coordinate representation for every arbitrary-family completed input is
assumed; the general series theorem retains its exact HasSum hypothesis.

## Quantitative closure and remaining obligations

If norm(g(p)-h(p))<=delta at EVERY p, with delta>=0, then the actual completed
operators satisfy norm(M_g-M_h)<=delta. Uniform convergence of measurable bounded
multipliers with explicit errors tending to0 therefore gives OPERATOR-NORM
convergence, stronger than convergence on an individual input. The independent
tests also verify convergence of the associated actual stochastic L2 outputs.
No pointwise-only, dominated-only, unbounded multiplier or pathwise convergence
extension is claimed.

This closes the joint-kernel and bounded predictable multiplier completion gap.
It does NOT yet identify J M_g z with an independently constructed ordinary
Itô integral against the single terminal martingale P_t Jz for all g. The next
concrete connection is the elementary raw-adapted rectangle pull-out identity
1_A(P_t-P_s)Jz and its original coefficient/grid approximations, followed by the
needed stronger closure. Operator multiplication laws alone do not prove that
stochastic associativity theorem. Conditional temporal-gradient Clark–Ocone,
physical-time Itô/Tanaka for actual rough IBM, sample-path brackets/regularity
and the full intrinsic calculus remain open beyond earlier exact scopes.
In particular sign(IBM_T) is not automatically predictable at earlier times;
this theorem does not bypass that obstruction. IBM remains ACTIVE.

Verification requires the fresh full root build, complete transitive safe
Foundation axiom audit, all63 unabridged new interface types (including the
record constructor, fields and three eliminators),12 printed old/new definitions,
all462 final source/proof lines, eight independent tests, prior source/config
identity,113 immutable archive paths/hashes, ledger, exact Git receipt and
verified PRIVATE main/research refs. Timings, codes and development diagnostics
are recorded in the verification JSON. No new trust, toolchain, proof resource,
source deletion or suppressed check is introduced. Style warnings are retained;
the deprecated scratch apply aliases were replaced before final verification.
