# Actual intrinsic IBM divergence: full projected-source graph closure

Checkpoint1299, October21,2026. Active campaign: intrinsic calculus for actual
IBM. The frozen pseudoprocess checkpoint and queued later campaigns are unchanged.

## The domain gap being resolved

Checkpoint1107 proved that the joint intrinsic derivative D is closed and dense
on the actual IBM-observable Hilbert subspace V of the constructed independent
scenery/clock source space H. It defined delta=D* on its natural domain and
proved the conditional projected-sum identity on pairs of ambient source-adjoint
integrands. That was a one-sided inclusion; it did not identify the whole
intrinsic divergence domain with the unclosed ambient pair domain.

The new result identifies the FULL intrinsic divergence by graph completion.
Let A and B be the existing actual scenery and clock derivatives, with field
space K. Define S on K x K (with its two-channel Hilbert norm) by

    Dom(S) = Dom(A*) x Dom(B*),
    S(a,b) = P_V(A*a + B*b).

Here P_V is the already verified conditional projection onto the actual
IBM-generated sigma algebra. Then

    S* = D,       closure(S) = D* = delta.

This is an equality of actual partial operators and hence of their full graphs
and natural domains after closure. It does not assert equality of Dom(S) and
Dom(delta), an explicit inverse, or a stochastic predictable representation.

## Proof and exact theorem reuse

`ObservableProjectedDivergenceCore.projected_adjoint_eq_restriction` first
proves (P_V A*)* = A restricted to V for every closed densely defined source
operator on real Hilbert spaces. The converse direction uses the verified
closed bidual identity; the projection pairing turns a representer for the
projected operator into an ambient bidual graph point. This identity itself
does not require the restricted derivative domain to be dense.

`projected_closure_eq_adjoint` additionally requires that restricted domain
to be dense. The earlier closability/inclusion results and verified closable
bidual identity then identify the entire graph closure, strengthening the
previous one-sided `ObservableProjectedDivergenceClosure` result. Existing
definitions and older conclusions are preserved.

For actual IBM, `IBMIntrinsicDivergenceClosure.ambientPairOperator_dense` uses
the separately proved density of both ambient adjoints. Its adjoint is the
joint intrinsic derivative: testing (a,0) and (0,b) recovers the two derivative
graphs through the preceding single-channel theorem. The existing
`IBMJointIntrinsicDerivative.joint_graph_iff` assembles them on their full
intersection domain. The reverse inclusion reuses `ambient_pair_duality`.
The established joint domain density then gives closability and the exact
bidual closure. No density of a new ambient joint derivative is assumed.

The finite-channel assembly and strong graph-sequence extraction are small
generic helpers needed by this proof; no process, measure, chaos construction,
toolchain or stochastic axiom has been added.

## Operational convergence statement

`full_graph_approximation` states: for EVERY u in Dom(delta), there exist
genuine ambient source-adjoint integrands a_n,b_n such that

    (a_n,b_n) -> u                 strongly in the two-channel field L2,
    P_V(A*a_n+B*b_n) -> delta(u)   strongly in intrinsic observable L2.

`strong_graph_limit` proves the converse: these two strong limits force
membership in the natural intrinsic divergence domain and determine its value.
The sequences are existence constructions from actual graph closure, not an
explicit cylinder approximation algorithm. Neither weak convergence nor
convergence in distribution is substituted for either norm limit.

Only the projected SUM must converge. Neither unprojected divergence, nor even
the two projected terms separately, is required to have an L2 limit. This
distinction permits cancellation between channels and removal of invisible
components under conditional expectation. Requiring separate source divergences
to converge would impose an unproved stronger domain condition.

## Independent checks and scope

Independent Lean regressions check ordered channel evaluation, signs, cancellation
and the finite-product inner-product normalization. Exact rational tests check
projected pairings in nontrivial finite-dimensional observable subspaces and
truncations illustrating why unprojected values must not be the convergence
criterion. Their code and results are retained in the verification record.

For the latter warning, the standard diagonal operator (Ax)_j=j*x_j on l2
has domain sum_j j²*x_j² < infinity. The truncations of x_j=1/j are Cauchy
in l2 (the squared tail is <=1/N), while ||A x_N||²=N. Projection onto the first
coordinate makes the projected values constant. In a repeated two-channel
version, (x_N,-x_N) has identically zero summed divergences. The exact finite
tests validate these computations; this example is an explanatory mathematical
counterexample to stronger abstract convergence requirements, not a new Lean
identification of a strict domain gap for actual IBM.

## What remains open in the broader IBM campaign

This discharges the projected ambient versus intrinsic divergence GRAPH-CLOSURE
identification. It does not prove unclosed-domain equality, that every source
approximant is predictable, or that the approximating integrands are cylinders.
The integral is the actual closed Hilbert adjoint; a general intrinsic adapted
stochastic integral, intrinsic Clark–Ocone, chain/product rules, and a full
unmollified Itô calculus still require their own process/domain proofs.
The existing F1 common-clock dual and F2 literal boundary-layer conclusions
are retained with their original topologies, not enlarged by this result.

A productive next target is to determine whether the existing Gaussian
polynomial/step graph cores and predictable constructions give explicit
intrinsic approximants compatible with this full divergence closure. Audit
their exact core and conditional-projection hypotheses before transferring
adapted integration or claiming a natural IBM representation.

## Verification and preservation

`STARDUST_IBM_DIVERGENCE_CLOSURE_VERIFICATION.json` records final full-root build,
complete transitive safe-Foundation axiom audit, unabridged public-type and
source review, independent regressions and hashes. The committed record has
honest precommit backup status; the exact receipt and private branch verification
are recorded separately after commit. All prior Lean sources remain byte-identical
apart from the root imports of the two new modules. All113 manuscript paths and
hashes remain unchanged; manuscripts, unrelated drafts and caches are preserved.
