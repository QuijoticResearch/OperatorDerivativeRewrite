# Actual IBM-germ deterministic stochastic integral — checkpoint1316

IBM remains active. The integral constructed here acts on an explicitly defined
closed subspace of deterministic time L2 for the actual energy measure. It is
not the full predictable random-integrand calculus, nor a claim that the
right-germ martingale agrees with the original raw martingale at positive time.

## Reuse and exact construction

Checkpoint1314 constructs the actual scalar martingale r in the explicit
right-continuous ambient-null augmented IBM filtration G. Checkpoint1315 proves
strong L2 right continuity and constructs its actual countably additive energy
measure nu, with nu((s,t])=E(t)-E(s), E(t)=||r_t||^2. All of these objects, the
original joint probability law, and the original IBM process are reused.

`IBMRightGermDeterministicIntegral.covariance` proves

    inner(r_s,r_t) = E(min(s,t)).

It follows from the actual martingale projection identity and symmetry of the
Hilbert projection, not an independence or Gaussian increment assumption.
Define timePrefix t as the L2(nu) class of 1_(0,t]. Its inner product with
timePrefix s is nu((0,min(s,t)]), hence the same E(min(s,t)). All interval
measures are finite by the verified energy theorem. This gives equal Gram
matrices for the actual time indicators and actual random variables r_t.

For a finite real dictionary a of nonnegative times, `timeDictionary a` is
sum_t a(t)*timePrefix t and `stochasticDictionary a` is sum_t a(t)*r_t.
Both are actual linear maps built with existing Finsupp linear combinations.
The Gram identity proves equality of ALL paired dictionary inner products and
norms. Consequently

    stochasticDictionary a = stochasticDictionary b
      iff timeDictionary a = timeDictionary b.

Equality on the right is equality of actual time-L2 classes, so energy-almost-
everywhere equality of finite time-integrand presentations suffices. This
handles overlapping intervals, arbitrary finite dictionaries and different
partitions without a common strictly ordered grid assumption. It is a theorem
for deterministic coefficients, not for arbitrary random predictable fields.

For s<=t, the dictionary delta_t-delta_s represents the ACTUAL indicator
1_(s,t] in time L2. Its stochastic image is r_t-r_s. General real coefficient c
gives c*(r_t-r_s), and finite dictionaries agree almost surely with their actual
scalar sums on the original joint sample space. The interval-indicator identity
uses the disjoint union (0,s] union (s,t]=(0,t], not a formal notation convention.

## Completed domain, uniqueness, and convergence

`IBMRightGermIntegralCompletion.domain` is exactly the topological closure of
the range of timeDictionary inside L2(nu). The canonical dictionary embedding
has PROVED dense range in this specified domain, by the existing range/closure
topology lemmas. Its norm equality with the stochastic dictionary is proved.
Mathlib's `LinearMap.extendOfIsometry` therefore gives an actual linear isometry

    integral : domain -> JointL2.

It agrees with every finite dictionary and interval stochastic sum. Its actual
scalar realization satisfies

    integral_omega (integral(f)(omega))^2 d jointMeasure = ||f||^2_(L2(nu)).

For ANY filter and any dictionary approximations converging to f in the domain
norm, the actual stochastic dictionaries converge STRONGLY in scalar L2 to
integral(f). No weak/probe-only limit is substituted. The extension is unique
among linear isometries agreeing with those finite dictionaries. This is a
genuine stochastic integral on its stated completed domain, connected to the
actual random increments and the verified Hilbert operator extension machinery.

## Remaining obligations

This checkpoint does not prove that the interval-generated closed domain is
ALL of time L2(nu). The usual density assertion requires a separate applicable
measure-generation/approximation theorem; it is not assumed from the definition
of closure. The proved domain is complete and its embedding is dense in that
domain, but those facts alone do not imply full-space density.

Random predictable integrands require their actual coefficient-weighted
increment energies. The deterministic energy measure must not be factored out
as if increments were independent of the past or had deterministic conditional
variance. The existing bounded random-step/countable-grid results concern the
original raw M/F, not automatically the new r/G. Their law-free algebra and
conditioning arguments can be reused only with actual hypotheses checked.

Full-space deterministic density, random predictable completion/control,
compatibility with intrinsic native derivative/adjoint domains, Clark–Ocone,
regular versions, pathwise bracket and unsmoothed IBM Itô calculus remain open.
The original raw-M modification condition J_t=0 remains open at positive time.
No Brownian innovation, predictable representation property or full intrinsic
IBM calculus is claimed. All F1/F2 correction and K domains remain unchanged.

## Verification contract

`STARDUST_IBM_DETERMINISTIC_INTEGRAL_VERIFICATION.json` records the fresh full
root build, complete transitive safe-Foundation axiom audit, all 25 unabridged
public types, complete 179-line source/proof review, four independent Lean
tests, prior source/configuration identity and all 113 manuscript paths/hashes.
Tests check actual interval-indicator/increment identification, arbitrary
energy-a.e. presentation independence, strong completion convergence with the
actual integral isometry, and the shared energy of overlapping intervals.

The audited commit, exact receipt and verified PRIVATE main/research backup
close the checkpoint separately. The precommit report does not certify those
steps before they actually succeed. ResearchSources and the queue are unchanged.
