# Actual IBM stochastic integration and the native Gaussian divergence

Checkpoint1335 constructs an explicit bounded transfer from the ACTUAL full
predictable energy L2 integral into the EXISTING native intrinsic divergence
domain. It proves a genuine integration-by-parts identity and an exact
native-gradient/covariance-adjoint identity. The native derivative and
divergence are the old closed operators, not new names assigned to the
stochastic integral. IBM remains ACTIVE; full intrinsic calculus is not claimed.

## Exact theorem and domains

Let D=IBMJointIntrinsicDerivative.jointDerivative, with its existing dense
maximal source/clock intersection domain on IntrinsicSpace. Let delta=D* be
the existing jointDivergence. For every terminal F and every H in ALL actual
raw-predictable L2(mu_F), let I_F H be the verified completed integral1333.
The new actual nativeField, also expressed as the continuous linear map B_F,
satisfies

    B_F H belongs to Dom(delta),
    delta(B_F H) = I_F H, as an actual IBM-observable L2 class,
    norm(B_F H)^2 <= 2 * norm(H)^2.

For EVERY f in the EXISTING full Dom(D), this gives

    inner(I_F H, f) = inner(B_F H, Df),
    B_F.adjoint(Df) = I_F.adjoint(f).

Here the scalar observable f is embedded in original JointL2 when applying
the integral's bounded Hilbert adjoint. No new derivative-domain assumption
on I_F H is needed. The observable f in the pairing MUST lie in Dom(D).
The native field is a pair of actual Gaussian source/clock L2 fields, with
their original source Hilbert codomain. It is not asserted time adapted.

## Actual stochastic outputs are observable and centered

IBMPredictableIntegralObservable proves that every rightPast(t) class belongs
to the actual entire IBM-observable subspace: rightPast(t) is contained in
past(t+1), and the already verified finite past belongs to IntrinsicSpace.
Actual finite stochastic steps lie in their existing rightPast spaces.
Consequently every finite stochastic sum is intrinsic. Full actual dictionary
approximation and closedness of the actual observable subspace prove that
EVERY completed I_F H is intrinsic, not just cylinders or bounded steps.

Every actual finite step is orthogonal to rightPast(0), by the existing germ
martingale step theorem. This survives finite sums and strong JointL2 limits.
Thus every completed output is orthogonal to the entire initial right germ.
The genuine constant-one class belongs to raw past(0), hence to rightPast(0),
so every output is centered. This does NOT prove triviality of the initial
germ, nor set G^F_0=0 for arbitrary F.

## Constructed recovery in the ORIGINAL source graphs

IBMNativeGaussianRecovery reuses GaussianBochnerDivergenceRecovery's actual
bounded fiber recovery, BochnerLiftAdjointInclusion's proved adjoint inclusion,
and IBMIntrinsicOperators' exact native unitary transports. These give

    delta_clock R_clock(f) = f - P_clock(f),
    delta_source R_source(f) = f - P_source(f),

as genuine ambient native adjoint graph statements. P_clock and P_source are
the actual zero-sector projections in their respective probability factors;
neither is the IBM observation projection. Only the already proved one-sided
fiber-to-adjoint inclusion is used; no equality of full adjoint domains.

Use the pair R(f)=(R_source(P_clock f), R_clock f). The EXISTING projected
ambient-pair divergence theorem puts this actual pair in Dom(delta), with
value the IBM-observable projection of f-P_source(P_clock f). This retains the
two-factor vacuum remainder until it is proved to vanish in the centered case.

## Exact two-factor mean calculation

IBMNativeVacuumProjection verifies all factor orderings with the existing
product/Bochner L2 equivalence and flip. The actual fiber zero-sector equals
the tensor of its scalar fiber mean and Gaussian constant one. Source and
clock unitaries are related by the verified actual flip, not by an assumed
pointwise representative of an arbitrary nested L2 class.

The vacuum tensor pairing equals the outer Gaussian mean of the fiber mean.
The actual original-law constant one is transported to the actual Gaussian
vacuum tensor. Thus original global centering implies the outer mean of the
fiber mean is zero. Applying the two vacuum projections therefore gives zero.
No global centering is confused with separate centering in each factor.

As a result, EVERY centered intrinsic observable f, even outside Dom(D), has
the explicit native divergence preimage R(f). The observable projection fixes
f, so delta(R(f))=f. Each one-factor recovery is contractive by the EXISTING
Gaussian recovery theorem, and P_clock is contractive by the EXISTING source
projection theorem. The pair's squared norm is the sum of squared component
norms, giving norm(R(f))^2<=2*norm(f)^2. No optimality or uniqueness claim is made.

## Bounded transfer and the operator-calculus connection

IBMNativePredictableTransfer proves R is linear and constructs its actual
continuous linear map with bound sqrt(2). Set B_F=R composed with I_F. This
is a constructed bounded linear map from genuine predictable energy L2 into
the EXISTING JointFieldSpace. It is not an unspecified field chosen separately
for each random variable. Its values equal the nativeField construction.

Actual observable/centering results make delta B_F=I_F. Existing full-domain
Hilbert adjointness then proves integration by parts. Pairing against EVERY
H and using equality of Hilbert-space vectors proves B_F* Df=I_F* f exactly
on Dom(D). This is an actual connection between the native source derivative
and the stochastic covariance adjoint. It is not obtained by defining D=I_F*.

## Limits, counterexamples and remaining obligations

B_F is generally not a canonical causal projection of D, and no temporal
adaptedness, locality or minimal norm of its two-channel field is asserted.
The recovery order clock-then-source is explicit. The adjoint identity does
not assert I_F I_F* f=f for all centered observables: range reconstruction
or the corresponding residual-zero theorem is still required for that claim.
F-dependent terminal channels do not supply universal driving noise.

An independent test explicitly rules out uncentered reconstruction: one is
not any actual stochastic output. It does not refute a correctly centered
Clark–Ocone formula. A separate actual coordinate test recovers observed(1)
as a native divergence of a NONZERO field, using the existing initial-coordinate
zero and terminal recovery theorems, without assuming observed(1) is in Dom(D).

Raw/G projection comparison, equality with old RAW terminal series, pathwise
regular versions/bracket, intrinsic chain/product/Itô formulas, causal native
derivative identification and general Clark–Ocone reconstruction remain open.
The existing full native graph-approximation theorem remains available on
the proved native domain; no redundant wrapper or new resource override is
needed. During development such a wrapper exceeded default elaboration budget
and was omitted because the existing theorem already supplies the statement.
No mathematical claim depends on that failed wrapper.

Focused F1–F3 exact1107 domains, original closed dense D/actual delta, all M/F/Z
definitions, prior stochastic laws, pseudoprocess freeze and campaign queue
are preserved. Further work should use this actual bounded transfer and exact
duality to investigate meaningful representation/causal/domain obligations,
without relabeling the completed divergence range construction as full IBM calculus.

## Verification

Five modules396lines/48 public declarations. Complete source/proof review,
actual unabridged public-type review, fresh complete root build, COMPLETE
transitive safe Foundation axiom audit and five independent Lean checks are
recorded in STARDUST_IBM_NATIVE_STOCHASTIC_DIVERGENCE_VERIFICATION.json.
All2144 prior sources except EXACTLY5 appended root imports, all3 configuration
hashes and all113 archive paths/hashes must be unchanged. No new proof-resource
override, axiom, source edit or suppressed error is allowed. Explicit-path
commit, exact-commit receipt and verified PRIVATE main/research synchronization
follow these gates. The indefinite goal and actual IBM campaign remain ACTIVE.
