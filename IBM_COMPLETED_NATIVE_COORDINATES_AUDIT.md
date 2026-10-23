# Predictable coordinate fields and native completed IBM calculus — checkpoint1369

Every input of the1368 fixed-family multichannel completion now has an explicit
coordinate representative, realized by a jointly measurable predictable field.
The completed stochastic integral is also connected to the ORIGINAL native
divergence, integration by parts and derivative adjoint. The graph-dual recovery
formula applies to ALL intrinsic observables, retaining the WHOLE initial-germ
prediction. These results do not identify a conditional temporal-gradient
Clark–Ocone formula or a physical-time IBM Itô–Tanaka calculus.

## Genuine fixed-family coordinates

`Foundation/IBMCompletedCoordinates.lean` reuses the1362 fixed countable family
and its existing integrands and Hilbert coefficients. For any completed input z,
take its ACTUAL stochastic output Jz, proved intrinsic and orthogonal to the
original initial germ. Define H_i as the old coefficient of Jz times the old
fixed integrand in channel i. These are actual elements of the ORIGINAL
L2(mu_(F_i)); no new coordinate domain or basis is selected.

The old stochastic expansion and the proved zero initial prediction of Jz give
HasSum of the actual channel integrals to Jz. The actual full signed energy gives
the finite Gram-tail criterion;1368's series theorem then constructs a completed
sum w of the component embeddings. Since Jw=Jz and J is injective on the completed
NULL QUOTIENT, w=z. Thus this is a coordinate representative of EVERY completed
fixed-family input, not merely a representation of a smaller subspace of outputs.

The original coordinate Parseval identity proves

`HasSum (i -> norm(H_i)^2) (norm(z)^2)`.

This diagonal identity concerns the SELECTED canonical coefficient/integrand
family. It is not asserted for arbitrary random channel integrands; the verified
opposite-channel cancellation obstruction and the necessity of general signed
cross terms remain intact.

For each i, use the existing Lp measurable-representative operation to choose
an actual real function on Space=time×original-sample. It is measurable for the
ORIGINAL raw predictable sigma algebra, agrees with H_i mu_(F_i)-AE, and is
MemLp2 for that original energy measure. With the countable channel labels given
the discrete sigma algebra, the field on labels×Space is jointly measurable.
This changes neither the filtration nor the original process law.

The class of each actual field representative is PROVED equal to H_i. Both
completed-input HasSum and ACTUAL stochastic L2 HasSum are proved for these
classes. The individual field-square integrals have HasSum norm(z)^2. All
measurability, representative, integrability and reconstruction connections are
proved. Generic arbitrary-family coordinate realization remains open; the
fixed-family theorem is sufficient to represent every intrinsic remainder.

## Original native divergence of completed inputs

`Foundation/IBMCompletedNativeCalculus.lean` constructs the bounded transfer

`T_F = oldRecoveryOperator composed with J_F`.

For every completed input z, J_F z is intrinsic and orthogonal to the whole
initial germ, hence centered. The existing centered-observable recovery theorem
proves T_F z belongs to the ORIGINAL joint divergence domain, and its actual
divergence is the intrinsic observable represented by J_F z. Membership is
established, not inserted as a conditional premise. The existing recovery bound
gives norm(T_F z)^2 <= 2 norm(z)^2.

On each embedded original single-channel input, the new transfer agrees exactly
with the OLD native predictable transfer. For f in the ORIGINAL joint derivative
domain, original adjoint duality gives the completed integration-by-parts identity

`inner(J_F z, f) = inner(T_F z, Df)`.

Consequently `T_F.adjoint(Df) = J_F.adjoint(f)` on that ORIGINAL domain. No
extension of the ambient derivative domain is asserted.

## Full observable recovery and graph-dual characterization

For the fixed family, the adjoint J.adjoint(f) is exactly the inverse Hilbert
equivalence applied to the original remainder f-G0f. This is proved using
orthogonality to the WHOLE initial germ, not a constants-only centering argument.
Its norm equals norm(remainder f). Therefore

`J(T.adjoint(Df)) = f-G0f`

for f in the ORIGINAL derivative domain, with the exact corresponding energy.

For EVERY intrinsic L2 observable f, each completed z supplies a genuine original
divergence-domain field T_F z and hence a genuine full-adjoint-graph test. Its
pairing with the existing graph-dual derivative equals inner(f,J_F z). The unique
Riesz vector in the completed stochastic integrand space satisfying ALL these
pairings is J_F.adjoint(f). For the fixed family, this yields

`J(J.adjoint(f)) = f-G0f`

for EVERY intrinsic f, with no ordinary derivative premise. This identifies the
bounded stochastic-input recovery through native graph-dual pairings. It does
not represent the ENTIRE graph-dual derivative by an ordinary ambient source field.

The earlier theorem that positive-time IBM observables lie outside the original
clock/joint derivative domain, and their graph-dual derivatives are not ambient-
field representable, remains true. Independent tests explicitly combine those
obstructions with the new predictable-field stochastic reconstruction. There is
no contradiction: the recovered stochastic integrand and the full ambient
derivative have different codomains and characterizations.

## Remaining scope and verification

The native recovery map is built from the old recovery operator and stochastic
isometry. No theorem here identifies it, its adjoint, or the selected coordinate
field with conditional expectations of a temporal derivative. Causal temporal
Clark–Ocone, physical-time Itô–Tanaka and pathwise bracket obligations remain
open beyond exact earlier results. Full intrinsic IBM calculus is incomplete
and ACTIVE. No later campaign begins.

Preserve the full root build, complete transitive safe Foundation axiom audit,
all37 final public types, twelve printed definitions, ALL253 final source/proof
lines, independent actual-object tests, old source/configuration and113 immutable
archive path/hash checks, exact Git receipt and verified PRIVATE main/research
refs. Exact gates, timings, codes and failures are recorded in the verification
JSON. Native scratch rewrites hit the DEFAULT200000-heartbeat elaboration limit;
explicit adjoint equalities and typed intermediate inner products repaired the
proof without any resource increase, new axiom, prior-source change or weakened claim.
