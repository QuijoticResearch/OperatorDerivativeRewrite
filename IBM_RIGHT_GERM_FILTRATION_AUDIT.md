# Actual IBM right-germ martingale in an explicit filtration — checkpoint1314

IBM remains active. This checkpoint realizes the previously constructed scalar
right germs as a genuine martingale on the original joint probability space.
It does not establish that they are a modification of the original martingale.

## Objects and exact theorem

Write F_t for the unchanged raw natural filtration of actual IBM and M_t for
the verified optional projection of the quadratic clock martingale. Existing
checkpoint1313 defines R_t as the intersection of all L2(F_u), u>t, and
r_t=P_{R_t} M_T for any T>t. Its canonical scalar representative is rightValue t.

The new module `Foundation/IBMRightGermFiltration.lean` defines

    G = (AmbientNullAugmentation.filtration jointMeasure naturalFiltration).rightCont.

Thus G_t is the intersection, over u>t, of the ambient-null augmented F_u.
This is an explicitly new filtration. It contains F_t and is right continuous
by Mathlib's actual IsRightContinuous predicate. Actual IBM remains strongly
adapted, by its original raw adaptation and filtration inclusion.

The principal theorem is
`IBMRightGermFiltration.actual_martingale`:

    Martingale rightValue germFiltration IBMSourceLaws.jointMeasure.

All random variables here are actual scalar functions on the existing joint
sample space, with its existing probability law. There is no hypothetical law,
new process axiom, independent-increment assumption or replacement clock.

## Representative and conditional-expectation identification

The essential domain theorem is `germPast_eq`: L2(G_t)=R_t. Its two directions
are proved rather than assuming sigma-algebra intersections commute with
almost-sure equivalence classes.

First, a G_t-measurable L2 class is measurable in every augmented F_u, u>t.
Existing conditional-expectation invariance under ambient-null augmentation,
and recovery of an integrable measurable function by conditioning, imply that
it has an F_u-measurable version. Hence it belongs to every L2(F_u).

Conversely, the canonical representative of any L2 class in R_t is ambient
measurable and has an F_u-measurable version for every u>t. The existing
ambient-null augmentation theorem makes this SAME representative pointwise
measurable in every augmented F_u. Its comap is therefore below their infimum,
so it is G_t-measurable. No uncountable intersection of full-measure events is
used. This uses the established ambient-null construction, not an assertion
that the original measure space or original filtration has usual conditions.

The L2 conditional-expectation theorem now identifies conditioning on G_t with
orthogonal projection onto R_t. These spaces increase with time. Nested
orthogonal projections, together with the already proved future-horizon
independence, give P_{R_s} r_t=r_s for s<=t. Combining this identity with strong
adaptation proves the full actual martingale predicate. Its L2 integrability
and norm bound ||r_t||^2<=2t^2 were already proved at checkpoint1313.

## Limits, unresolved obligations, and next direction

The unchanged original conditional identity E[rightValue_t|F_t]=M_t remains
valid. Equality rightValue_t=M_t almost surely holds exactly when the verified
jump class J_t=r_t-M_t vanishes. It vanishes at zero; vanishing at positive
times is still open. The new theorem does not prove raw F right continuity,
raw sigma-intersection/L2 commutation, or a modification of original M.

No jointly time/sample measurable, right-continuous or cadlag version is
constructed here. Right continuity of G alone is not a path-regularity proof.
The next productive question is strong L2 right continuity of r itself, then
an actual regular-version/energy-measure construction with its hypotheses
checked. Common-refinement, continuum predictable-domain, intrinsic adjoint,
Clark–Ocone and unsmoothed IBM Itô obligations remain; full IBM calculus is open.
All previous F1/F2 correction terms, native domains and K-smoothing limitations
remain in force. The campaign queue and manuscripts are unchanged.

## Verification evidence

The fresh complete root build, complete transitive safe-Foundation axiom audit,
all 15 unabridged public types, all 113 source lines, and four independent Lean
tests are recorded in `STARDUST_IBM_RIGHT_GERM_FILTRATION_VERIFICATION.json`.
Tests check an actual conditional identity at times 1 and 2 together with IBM
adaptation; arbitrary intersection-class representative measurability; explicit
new-filtration right continuity and raw inclusion; and the original conditional
projection with the unresolved zero-jump equivalence retained.

All prior Foundation sources, the three configuration files and all 113
manuscript paths/hashes are checked against the checkpoint baseline/inventory.
Only the new module and its root import add mathematics. The exact-commit
receipt and verified PRIVATE main/research synchronization close the checkpoint
separately; precommit evidence does not claim those steps have already occurred.
