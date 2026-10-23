# Genuine random multichannel IBM energy completion — checkpoint1368

The general signed-energy null quotient and Hilbert completion of arbitrary
families of ORIGINAL predictable IBM integrands are constructed. Their integral
is a genuine linear isometry into the original stochastic L2 space, agrees with
all actual single-channel integrals, and has exactly the closure of their finite
sum range. For the1362 fixed countable actual channel family, its range is
precisely the full intrinsic observable space orthogonal to the ORIGINAL initial
germ. This is an actual Hilbert-space identification, not a temporal-gradient
Clark–Ocone theorem or a physical-time IBM Itô formula.

## Reuse and exact domain

`Foundation/IBMMultichannelCompletion.lean` reuses the1367 literal signed covariance
identity for ALL original separate L2 inputs,1362's fixed actual channel family,
the old all-channels range theorem, and pinned direct sums, module kernel
quotients, induced Hilbert norms, uniform completion and isometric extension.
No new generic completion, stochastic process, filtration or derivative is built.

For any indexed family of old terminals F_i, `Raw F` is the dependent direct sum
of the full ORIGINAL spaces L2(mu_(F_i)). Elements have finitely many active
channels, with arbitrary original random predictable integrands on each channel.
There is no boundedness, common-grid, deterministic-integrand or diagonal
orthogonality assumption. The construction works for arbitrary index types,
including countable ones. The DecidableEq index parameter and local component
instances are ordinary Lean bookkeeping, available classically; they impose no
analytic restriction on the family.

The raw linear integral is exactly the finite sum of the original actual
single-channel stochastic integrals. The verified energy pairing is the full
double sum of LITERAL signed integrals

`Gamma(u,v) = sum_i sum_j integral u_i v_j dnu(F_i,F_j)`.

Every scalar integrability premise is discharged by1367. Theorem `gram_actual`
proves Gamma(u,v)=inner(actualSum(u),actualSum(v)). Positivity follows from this
theorem, rather than an assumption or omission of signed cross terms.

## Null quotient and actual completion

The null submodule is the exact kernel of the raw ACTUAL stochastic integral.
It is proved equal to the zero-energy inputs. The algebraic quotient is mapped
injectively to the old actual finite-output range using the pinned first
isomorphism theorem. The induced norm and inner product are proved to recover
the full signed Gamma pairing on quotient representatives.

`Completed F` is the pinned UniformSpace.Completion of this genuine normed
quotient, with the pinned Hilbert-space structure. Its stochastic integral is
constructed through the verified isometric-extension theorem. Finite inputs
embed densely; their actual output and full signed energy are preserved.
Two finite families have the same embedded class exactly when their difference
has zero joint energy. The completion integral is unique among isometries that
agree with the original finite stochastic sums. No unfinished closability or
positive-definiteness hypothesis is concealed in this construction.

Its range is exactly the topological closure of the raw finite-output range.
The proof uses completion induction and closedness of the actual isometric
range. Every output is intrinsic and orthogonal to the WHOLE original initial
germ. It does not replace that germ by constants or silently complete/change
the filtration.

## Fixed countable family and reconstruction

The old1362 channel family is reused without selecting new channels for each
target. Its old scalar-integrand reconstruction is used to prove that the NEW
completion, allowing arbitrary random original integrands in those channels,
surjects onto `IntrinsicSpace intersect (rightPast 0).orthogonal`.

`fixedHilbertEquiv` is a proved linear isometry equivalence between the actual
completed quotient and that remainder space. Its inverse supplies the unique
completed quotient input reconstructing every intrinsic observable minus its
original initial-germ prediction. Uniqueness is in the completed null quotient,
not uniqueness of a coordinate integrand before quotienting. No identification
with a conditional temporal derivative, independence of noises, causal-gradient
formula or new semimartingale law is asserted.

## Countable series and convergence topology

For any family of old completed single-channel integrands H_i, the finite full
signed energy of a set t equals the squared norm of the finite sum of embedded
inputs AND of the actual stochastic sum. The theorem `series_iff_energy_tails`
proves the exact criterion

`for every eps>0, some finite s has Gamma_t(H,H)<eps^2 for every finite t disjoint from s`.

This is equivalent to unconditional summability in the completed quotient.
It retains ALL cross terms and does not replace the condition by a sum of
diagonal energies. Under that criterion `series_realization` constructs an
actual completed input and proves HasSum convergence there and strong stochastic
L2 HasSum convergence of the ACTUAL channel integrals to its stochastic output.
The finite-subset topology is explicit; arbitrary divergent fields are not
declared integrable, and no ordering-dependent sum is substituted.

## Remaining calculus obligations

The random multichannel energy completion/null-quotient obligation is now
resolved in this exact sense. Completed inputs are joint-energy classes and
limits. No theorem here supplies a coordinate family or a jointly measurable
time-index field for EVERY completed input of an arbitrary channel family;
such representative questions retain their own domain and uniqueness issues.
In the fixed-basis case the old scalar-coordinate expansion is a promising
route to an explicit representative theorem, but it is not proved here.
This does not settle the intrinsic temporal
gradient and causal Clark–Ocone identification, physical-time Itô–Tanaka or
pathwise brackets. The old rough-domain counterexamples and F1–F3 theorem
scopes remain intact. A productive next step is to connect this actual completed
space to the existing native divergence and derivative-adjoint machinery,
with precise domain and causal qualifications. Full IBM remains ACTIVE and
incomplete; no subsequent campaign starts here.

## Verification and preservation

Retain the fresh full root build, complete transitive safe Foundation axiom
audit, all46 named new declarations (including local dependent-component helpers
and quotient instances), thirteen printed old/new definitions, ALL249 final
source/proof lines, and independent Lean tests. These test single-channel
agreement/norms, full Gram/isometric equivalence, an ACTUAL nonzero opposite-IBM1
raw input killed by the null quotient, finite signed energy, point-time observed
reconstruction, quotient uniqueness, joint-energy series and energy convergence,
and orthogonality to the original initial germ. Exact terminal results, test
code and development diagnostics are in the verification JSON.

One scratch proof hit the original default elaboration limit. Explicit index
decisions, function/coercion transports and finite-sum proofs repaired it without
raising any resource limit. No proof semantics, source manuscript, toolchain,
axiom whitelist or verification gate is changed. Old source/configuration and
all113 manuscript path/hash checks remain mandatory, followed by exact Git audit
receipt and verification of BOTH private remote refs. The saved queue is unchanged.
