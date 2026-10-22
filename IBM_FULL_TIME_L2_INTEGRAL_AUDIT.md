# Full deterministic time-L2 stochastic integral — checkpoint1317

IBM remains active. The interval-density gap from checkpoint1316 is resolved:
its specified closed domain is ALL L2 of the actual right-germ energy measure.
This extends the actual deterministic stochastic integral, not the random
predictable domain and not a claim of completion of intrinsic IBM calculus.

## Actual measure and density hypotheses

The existing energy measure nu on nonnegative time is unchanged. It is locally
finite, has no mass at zero, and has finite mass on every (0,T]. The source
`IBMRightGermIntervalDensity` first proves that Iic T and Ioc 0 T agree nu-almost
everywhere, and hence that Iic T has finite mass. The missing endpoint at the
bottom of nonnegative time is handled explicitly rather than overlooked.

Let D be checkpoint1316's closed range of finite prefix dictionaries. Every
actual prefix class 1_(0,t] belongs to D. If f belongs to its Hilbert orthogonal
complement, the existing L2 inner-product/set-integral identity shows that
integral_(0,t] f dnu=0. Zero origin mass then gives integral_Iic t f dnu=0.

Fix T. Since f is genuinely L2 and nu(Iic T) is finite, it is integrable for
the RESTRICTED actual measure nu|Iic T. Form that measure's existing vector
measure with density f. On any Iic t its value is the integral over Iic(min(t,T)),
which is zero. Its value on the whole space is the integral over Iic T, also
zero. The family of Iic intervals is a pi-system and generates the actual
NNReal measurable space by its verified Borel-space and order-topology results.
`VectorMeasure.ext_of_generateFrom` therefore identifies this actual vector
measure with zero. The existing integrable-density uniqueness theorem implies
f=0 almost everywhere on Iic T.

The horizons T=n cover all nonnegative real time. The countable restricted-AE
union theorem now yields f=0 in the full actual time L2 space. Thus D has zero
orthogonal complement. D is closed in the complete Hilbert space, so the
existing projection/orthogonal theorem yields `domain_eq_top`. In particular,
`timeDictionary_dense` is density in ALL time L2, not merely in D. No finite
total mass, global L1 integrability, unspecified completed measure, or uniform
convergence of representatives is assumed.

## Full deterministic stochastic integral

`IBMRightGermFullDeterministicIntegral.integral` uses the existing dense-isometry
extension and the previously verified exact dictionary norm identity to give

    integral : Lp Real 2 energyMeasure -> JointL2

as an actual linear isometry. It preserves all paired inner products, and its
actual scalar squared integral equals the time-L2 squared norm. On every
interval indicator 1_(s,t], s<=t, its value is exactly r_t-r_s, with the actual
scalar almost-sure realization inherited from the existing Lp bridge. On every
finite dictionary it agrees with the actual stochastic sum.

Every time-L2 class admits a sequence of actual finite dictionaries converging
in the time-L2 norm, and the corresponding actual scalar stochastic sums
converge STRONGLY in JointL2 to its integral. This existence result follows from
full density and the actual sequential closure theorem in this metric space.
The general approximation-limit theorem still holds for every filter, not only
sequences. The extension is unique among linear isometries agreeing with finite
dictionaries and agrees with the old completed-domain integral at every old
domain element. No prior mathematical result or original process is changed.

## Remaining intrinsic calculus obligations

The full deterministic domain gap is closed. This does NOT establish random
predictable-integrand completion, a random control measure or predictable
bracket. Actual random coefficient increment energies cannot be replaced by a
deterministic measure factor without an applicable conditional-variance theorem.
Earlier bounded random-step/countable-grid proofs concern original M/raw F;
transfer to the explicit right-germ r/G requires its actual hypotheses.

Native derivative/adjoint compatibility, Clark–Ocone/predictable representation,
jointly measurable regular versions, pathwise variation and unsmoothed IBM Itô
remain open. The original IBM, raw filtration and raw M are unchanged; agreement
of r and M at positive times still requires the unresolved zero-jump condition.
All F1/F2 correction terms and K-domain limitations remain in force. Next use
the actual full integral and reusable operator machinery to address adjoints
and genuine random predictable integration, preserving those distinctions.

## Verification contract

`STARDUST_IBM_FULL_TIME_L2_INTEGRAL_VERIFICATION.json` records fresh full-root
build, complete transitive safe-Foundation axiom audit, all new unabridged
public types and complete proof review, four independent Lean checks, prior
source/configuration identity, and all 113 immutable manuscript paths/hashes.
Checks cover approximation existence for arbitrary full time-L2 inputs, actual
scalar interval-increment identification, paired covariance preservation and
injectivity, and agreement with the previous integral plus its actual isometry.

Exact Git receipt and verified PRIVATE main/research synchronization close the
checkpoint separately. Precommit evidence does not claim backup completion.
The research queue and manuscript bytes remain unchanged.
