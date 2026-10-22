# IBM native source recovery and ordered reconstruction — checkpoint1300

Active intrinsic IBM calculus; no queued campaign is activated. This builds on
the fully verified checkpoint1299 divergence graph-closure theorem.

The existing Gaussian inverse-number-gradient `recoveryOperator` and its
Bochner lift already produced genuine fiberwise divergence graph points.
Those statements alone did not place their fields in the native source
adjoints defining the actual IBM intrinsic calculus.

`BochnerLiftAdjointInclusion.lift_formal` now proves fiberwise integration by
parts on the actual Bochner L2 classes, by integrating the original almost
everywhere graph identities. `lift_adjoint_le` establishes

    lift(T*) <= (lift(T))*

when Dom(T) is dense. This is an inclusion, not an unsupported full equality
of lifted adjoint domains. No polynomial graph density or measurable selection
of arbitrary fiberwise witnesses is assumed.

`IBMNativeSourceRecovery` transports the EXISTING bounded Gaussian recovery
through the already verified native scenery/clock unitaries. It constructs
continuous linear maps R_s,R_c on the full actual joint L2 space, each of norm
at most one, with genuine ambient-adjoint graph identities

    A* R_s f = C_s f,       B* R_c f = C_c f.

Here C_s,C_c are the actual factorwise centerings, not supplied derivative
values. The module constructs the corresponding factor-zero projectors
P_s,P_c explicitly from Gaussian number-sector projection0 and proves
C_s f=f-P_s f and C_c f=f-P_c f. The native graph identities therefore hold
for every joint L2 target without a Sobolev-domain hypothesis on that target.
Their conditional intrinsic divergence identities are proved as well.

`ordered_intrinsic_reconstruction` assembles the actual pair

    U(f) = (R_s f, R_c(P_s f)),
    delta_intrinsic U(f) = P_IBM(f - P_c(P_s f)).

U(f) belongs to the ORIGINAL ambient pair-adjoint domain, not merely its graph
completion. The RHS is a genuine intrinsic observable, obtained by the existing
conditional projection onto the actual IBM-generated sigma algebra. For an
IBM-observable input, the first projected term is that input itself. Both
projectors and both recovery operators are defined independently of the final
identity. The residual has not been defined tautologically as a reconstruction
error.

The composed projector P_c P_s is retained literally. Identifying it in these
native coordinates with the actual global constant/expectation projector is
the next proof obligation. This checkpoint does not claim that identity is
Lean-verified, that every centered intrinsic observable is already reconstructed,
or that U(f) is predictable. In particular this is not a predictable
Clark–Ocone formula or an unmollified stochastic Itô formula. The static
recovery construction remains part of the active IBM campaign.

Independent Lean tests check Gaussian vacuum annihilation, including arbitrary
Bochner outer coefficients, using the older minimal-norm and fiber graph
machinery. Exact rational tests check ordered source/clock sector reconstruction
and inverse-number energy on 867 cases each. These finite tests are regression
evidence, not substitutes for actual infinite-dimensional graph proofs or the
remaining global-zero-mode identification.

`STARDUST_IBM_NATIVE_RECOVERY_VERIFICATION.json` records complete-root build,
complete transitive axiom audit, all19 public types and all179 source/helper
lines reviewed, independent test code/results, source hashes and timings.
Original2058 Foundation/root sources remain unchanged exceptroot twoimports;
all113 manuscript paths/hashes and3configuration files remain unchanged.
The committed verification record honestly precedes private receipt/sync;
exact private backup closure is recorded separately after commit. All existing
stochastic, source-integrity, Git and private-backup requirements remain in force.
