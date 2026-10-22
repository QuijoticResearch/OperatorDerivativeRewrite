# Actual predictable support energy and continuity inputs

Checkpoint1330 advances the joint predictable energy-measure obligation within
the ACTIVE IBM campaign. It constructs genuine finite stochastic sums for the
EXISTING right-germ terminal martingale and proves support-sensitive energy
control. A joint predictable measure or full continuum integral is not declared.

## Existing process, filtration and domains

Fix ANY actual JointL2 terminal F on IBMSourceLaws.jointMeasure. The integrator
is the EXISTING G^F_t = channelClass F t, whose actual representative is
channel F t and whose martingale filtration is the explicit augmented IBM
right-germ filtration. The new coefficients reuse the existing Coefficient s:
bounded real functions strongly measurable in the ENTIRE RAW observed IBM past
at s. Raw past embeds into the germ filtration. Coefficients are not restricted
to finitely many observed coordinates or polynomials.

This is not integration directly against the nonmartingale Z_t=W(abs(Y_t)).
The terminal F is fixed throughout every identity; its channel depends on F.
Nor is G^F silently identified with the earlier RAW prediction N^F at positive
times. Checkpoint1327's exact raw/germ comparison gate remains intact.

## Actual right-germ step and finite-presentation identification

IBMGermPredictableStep reuses checkpoint1327's ACTUAL weighted terminal aF
and conditional-expectation pull-out G^(aF)_u=a*G^F_u for u>=s. It defines

    stepClass F s t a = G^(aF)_t - G^(aF)_s.

For s<=t, the scalar AE bridge proves this is exactly a*(G^F_t-G^F_s).
There is no supplied hypothetical stochastic realization. Membership in the
terminal germ past, zero starting projection, and orthogonality to EVERY
earlier germ-past L2 observable follow from existing nested projections.
Nonoverlapping ordered steps are orthogonal. Exact energy is the actual
integral E[a^2*(Delta G)^2], with no variance-factorization assumption.

A further actual terminal pairing is proved:

    inner(F,step) = E[a*(Delta G)^2].

It uses the terminal projection at t and orthogonality at s, then the actual
scalar AE bridge. Thus for idempotent a (a^2=a AE), inner(F,step)=norm(step)^2.

IBMGermIndicatorSupport forms genuine finite L2 sums. For intervals with
s_i<=t_i and pairwise ENDPOINT separation t_i<=s_j or t_j<=s_i, orthogonality
gives their exact squared-norm sum. Gaps, unordered index labels and degenerate
intervals are allowed subject to those exact hypotheses. If each coefficient
is idempotent AE, the whole sum I satisfies inner(F,I)=norm(I)^2.

The actual finite stochastic sum is also independent of its finite interval
presentation whenever the two actual time processes agree AE at EACH time.
The existing deterministic endpoint-charge identity is applied to the actual
path r -> channel F r omega, then scalar AE bridges identify the two L2 sums.
This identification does not require temporal separation or idempotence;
only the intervals' ordering is required. No uncountable AE intersection or
assumed scalar path regularity is used.

## New support-sensitive domination

Let A be ANY ambient measurable sample event; it need not be measurable in
the starting past, or in any of the coefficient pasts. Suppose the finite
time process vanishes outside A AE at EACH time. The existing endpoint-charge
identity, applied only at the FINITELY many endpoints, proves its actual
stochastic sum I vanishes outside A almost surely. Cancellation between
overlapping steps is allowed in this support implication.

For a temporally separated family with idempotent coefficients, construct
the ACTUAL JointL2 terminal 1_A*F by MemLp.indicator and its scalar AE bridge.
The support statement gives inner(1_A*F,I)=inner(F,I)=norm(I)^2. Expanding
the nonnegative squared norm of (1_A*F-I) now proves

    norm(I)^2 <= integral_A F^2.

This is stronger than the previous global norm(F)^2 bound and retains the
actual original probability law. It supplies control for exceptional events
arising from whole time fibers, which generally are not adapted at the
initial time. No unsupported multiplication/pull-out by the arbitrary A
is used: only its actual ambient indicator terminal and the support identity.

The idempotence hypothesis is ESSENTIAL. An independent Lean counterexample
uses actual F=observed1 and constant coefficient2 on(0,1]. Checkpoint1329's
zero initial projection and terminal recovery give the actual step 2*F.
Its squared norm is 4*norm(F)^2 > norm(F)^2 since observed1 is nonzero.
Thus the proposed unit support bound would fail even with A=the whole space
if arbitrary bounded coefficients were substituted for indicators.

## Verified continuity mechanisms

IBMGermSupportContinuity proves integral_(A_n) F^2 ->0 if the A_n are ambient
measurable and almost every sample eventually leaves them. Actual dominated
convergence uses F^2, whose integrability is already verified by F in L2.
No assumed adaptation of A_n is introduced. Combining this with the new
support bound gives STRONG actual JointL2 convergence tozero for sequences
of the finite indicator stochastic sums; their finite index types, intervals,
coefficients and number of cells may all vary with n. Every member retains
its exact temporal separation, indicator and support hypotheses.

Independently, for ANY bounded raw-past coefficient at s and ANY horizons
tau_n>=s with tau_n->s, the actual step on(s,tau_n] tends strongly tozero.
This follows from the verified strong L2 right continuity of the EXISTING
weighted terminal channel G^(aF), not continuity of observed paths or an
assumed raw-filtration regularity theorem. No monotonicity of tau is needed.

## Next joint-extension argument: exact unformalized obligations

The new results suggest the following concrete route, which remains a plan
until its Lean obligations are proved. Encode the finite ring of eligible
predictable rectangles and normalized indicator presentations. Prove finite
additivity, differences/intersections, and compatibility with existing event
and time measures. In a decreasing sequence of finite-ring sets with empty
intersection, approximate each time fiber from inside by finite unions of
CLOSED time intervals, removing a right-neighborhood of each left endpoint.
The verified right-trim limit controls the energy error of the removed pieces.

Intersect finitely many such closed-fiber approximants. Within a finite time
horizon their fibers are compact. A decreasing family of nonempty compact
fibers cannot have empty intersection, so every sample eventually leaves the
projected support events. These projected events must be constructed and proved
measurable from the FINITE rectangle data; arbitrary measurable projection
theorems must not be assumed. The new support-sensitive estimate and dominated
convergence would then control the surviving energy, while summably small
trim errors control the discarded energy. This could prove continuity at
empty for the actual ring content, then the required JOINT sigma-subadditivity.

None of the finite-ring construction, compact-fiber assembly, measurable
projection construction, continuity-at-empty for arbitrary decreasing ring
sets, sigma-subadditivity or Caratheodory extension is claimed completed here.
Separate countable additivity of time/event slices remains insufficient.
Mathlib AddContent.measure and its exact hypotheses must still be satisfied.

## Verification, preservation and remaining scope

Three new modules295lines/24 public declarations. Complete sources/proofs
and actual unabridged public types are reviewed. Four independent Lean checks
cover a past-event coefficient supported in a container involving a FUTURE
IBM observation, actual terminal energy on shrinking IBM tail events, positive-
time right trimming with a random coefficient, and the constant2 counterexample.
Fresh full root build, COMPLETE transitive safe-Foundation axiom audit with
the same standard three allowed axioms and independent results are recorded
in STARDUST_IBM_PREDICTABLE_SUPPORT_ENERGY_VERIFICATION.json.

All2126 prior sources except exactly3 root imports, all3 configurations and
all113 archive paths/hashes must be unchanged. No manuscript is modified or
staged. All source-integrity, full-build, actual type/proof review, Git,
exact-receipt and verified PRIVATE main/research gates remain mandatory.

The completed focused F1–F3 theorems retain their exact checkpoint1107 domains,
including K-dual cross-sector convergence, literal boundary-layer L2 limit,
and the dense closed intrinsic derivative with its actual Hilbert adjoint.
Their stronger native integration/domain/representation connections remain
under investigation. Full initial-germ triviality, positive-time raw/G equality,
joint predictable extension, continuum random-integrand closure, regular scalar
versions/pathwise bracket and full intrinsic unsmoothed IBM calculus remain
OPEN. The initial-coordinate zero theorem1329 is preserved. Original M/F/Z,
all existing theorem domains and the linear campaign queue are unchanged.
