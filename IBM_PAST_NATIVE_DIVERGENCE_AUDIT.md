# Actual IBM past adjoint: native graph core and reconstruction — checkpoint 1305

IBM remains ACTIVE. This checkpoint connects checkpoint 1304's actual-past
derivative/adjoint to the existing native scenery and clock divergences and
checkpoint 1301's bounded source recovery. All horizons T≥0 are included.
It does not identify these source fields with temporal predictable integrands.

## Exact agreement with native source divergences

Write V for all-time actual IBM-observable L2, W_T for its actual raw natural
past, D for the existing joint source/clock derivative, and δ_T for the maximal
adjoint of its dense closed restriction to W_T. The previous checkpoint proved
that W_T represents the ENTIRE actual past, not a smaller differentiable subset.

`IBMPastDivergenceClosure.projectedFull_closure` directly reuses
`ObservableProjectedDivergenceCore.projected_closure_eq_adjoint` to prove

    closure_graph(P_W_T D*) = δ_T.

The independent density hypotheses are now the verified joint-domain density
and the verified actual-past common-domain density. Full intrinsic integrands
belong to the past adjoint domain, whose value there is their past-projected
intrinsic divergence. No equality of the initial unclosed domains is asserted.

The stronger `nativePair_closure` proves

    closure_graph[(a,b) ↦ P_W_T P_V(δ_source a + δ_clock b)] = δ_T,

on the genuine product of the EXISTING native scenery/clock adjoint domains.
The proof uses their established formal duality and checkpoint 1299's complete
intrinsic native graph approximation. Projection of that strong graph core
approximates every graph point of the projected full divergence. Closed graph
comparison then gives equality with the maximal past adjoint. No new formal
divergence is postulated, and no separate unprojected divergence convergence
or equality of their unclosed domains is assumed.

`full_native_graph_approximation` supplies native pairs for every maximal past
integrand: their fields converge strongly in the native two-channel Hilbert
space, while their past-projected SUM converges strongly in the actual past.

## Actual conditional expectation and its convergence topology

`IBMPastConditionalDivergence.projection_eq_condExp` identifies P_W_T P_V with
the genuine L2 conditional expectation under the existing constructed joint
probability law and its raw IBM natural filtration. It proves equality by the
actual closed-past projection's orthogonality characterization and the verified
inclusion W_T⊆V. `projection_ae_condExp` also gives the scalar almost-everywhere
conditional-expectation identity, with L2 representatives treated explicitly.

Consequently `full_graph_actual_condExp` proves that EVERY maximal past-adjoint
graph point is a strong limit of native pairs with

    E[δ_source a_n + δ_clock b_n | F_T] → δ_T u

in actual scalar joint L2, simultaneously with strong native-field convergence
(a_n,b_n)→u. `strong_graph_actual_condExp` proves the converse: those two strong
limits force membership in the maximal past-adjoint domain and identify its
value. The candidate scalar limit must be an actual past observable. Convergence
of conditional projected sums alone is not claimed to control fields, and no
individual unprojected divergence limit is required.

## Bounded actual-source reconstruction and exact range

`IBMPastSourceRepresentation.recovery_native_mem` places the EXISTING explicit
recovery pair in the native product domain for every joint L2 input. For every
actual past observable f, `native_centered_reconstruction` proves its projected
native divergence is f−E[f]1. Inclusion in the maximal past adjoint gives the
same identity in `past_centered_reconstruction`.

The constant 1 is proved to be an actual past observable and to have zero
past derivative. Domain-exact integration by parts then proves EVERY maximal
past divergence has mean zero. `range_iff_centered` gives its range EXACTLY as
the centered actual-past L2 space. `recoveryOnPast` is a genuine continuous
linear map obtained by restricting the existing recovery operator, with the
retained bound ‖R_T f‖²≤2‖f‖². No optimality or minimal-norm claim is made.

These are static source-valued reconstruction identities for the ACTUAL IBM
past. They neither make raw IBM a martingale nor establish an Itô integral
against it. The recovery fields are not proved predictable in IBM time.

## Verification and remaining obligations

Independent Lean checks preserve E[Z_2|F_1]≠Z_1, test constant normalization,
exercise the actual conditional-sum converse on arbitrary constant native pair
sequences, and refute reconstruction of the noncentered constant 1 without its
mean term. Full root build, complete safe-Foundation transitive axiom audit,
actual unabridged public-type/proof review, source manifests and manuscript
hash checks are recorded in `STARDUST_IBM_PAST_NATIVE_VERIFICATION.json`.
Six explicitly scoped 800000-heartbeat elaboration budgets handle nested
actual-source graph witnesses; these change no trust setting or proposition.
Pinned toolchain, Mathlib and permanent verification configuration are unchanged.

The central remaining issue is TEMPORAL: identify a natural-time causal or
predictable integrand realization and prove the convergence/closure statements
that connect it to these source fields and actual IBM Itô-type identities.
Conditional projection of values does not imply derivative/projection
commutation, preservation of derivative domains by conditioning, or predictable
field membership. Do not call the static representation temporal Clark–Ocone.
Preserve the proved F1/F2 correction terms and their exact topologies, and the
raw IBM nonmartingale obstruction. The latter does not exclude all corrected
or horizon-dependent temporal formulas or prove nonsemimartingale status.

Manuscripts remain immutable; the campaign queue and all verification/private
backup gates remain unchanged. No queued campaign has begun.
