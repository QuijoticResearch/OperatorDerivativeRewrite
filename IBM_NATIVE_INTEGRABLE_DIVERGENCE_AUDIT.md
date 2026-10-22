# Checkpoint1344 — actual contraction domain and deterministic IBM fields

The strong native divergence multiplier law now requires only actual
square-integrability of the TOTAL original-coordinate contraction. For bounded
f in the FULL ORIGINAL joint derivative domain and u in the ORIGINAL divergence
domain, assume

    sum_i <coordinate_i(D_i f), coordinate_i(u_i)> belongs to L2, i=0,1.

Then the actual native field M_f u belongs to that SAME divergence domain and

    delta(M_f u) = P_IBM (M_f(delta u) - actualContraction(Df,u)).

`IBMNativeIntegrableDivergence.weighted_mem` and `weighted_value` prove domain
membership and the exact value. Separate L-infinity bounds on Df are removed.
The contraction hypothesis is on the actual pointwise total, so it need not be
proved by separately placing each channel contraction in L2. No necessity or
maximal-domain theorem is claimed for this sufficient condition.

## Actual integrability and proof reuse

`IBMNativeContractionDomain.pairingFunction` is the sum of the two actual
coefficient inner products after the established source/clock coordinate maps.
`correction` is its actual L2 equivalence class under the stated MemLp proof.
The proof first uses L2 x L2 -> L1 for each channel and multiplication by a
bounded scalar test. This justifies splitting the integral and proves exact
pairing against checkpoint1342's native multiplier. It does not assume L2 x L2
-> L2. The existing strong bounded graph core, representer extension and actual
adjoint then yield the generalized law. All operators, measures, source
coordinates, projections and domains remain the original ones.

Two useful sufficient criteria are proved: coefficient fields u_i in L-infinity
paired with arbitrary native L2 gradients; and both sets of coefficient fields
in L4. They directly reuse the existing Holder-aware LpProducts results.

## Concrete, nonzero native divergence-domain fields

`IBMNativeDeterministicFields.directionField h` is the genuine Bochner tensor
of Gaussian one with the existing scalarTensor h Gaussian-one field. Its
adjoint membership comes from the verified first-chaos divergence graph,
Bochner lift-adjoint inclusion and native unitary transport. Pairing two such
fields gives a member of the ORIGINAL intrinsic divergence domain.

Their actual original-coordinate coefficient representatives are the constants
h and k, including the source-coordinate swap. Thus both fields are essentially
bounded. `native_source_ne_zero` proves the native field is nonzero whenever
h is nonzero. This is a nonzero FIELD statement; nonzero divergence of every
direction is not asserted. The construction does not assume that a generic
projected first-chaos scalar is nonzero.

For EVERY bounded f in full original Dom(D), multiplying these deterministic
fields by f preserves original Dom(delta), with its actual projected correction
formula. No gradient bound or extra contraction hypothesis remains in this
concrete application. The independent process-observable test constructs f
equal almost everywhere to sin(nativeAverage T) for every T >= 0, proves its
actual bound and full-domain membership using existing chain machinery, and
proves weighted membership for every h,k. The native average is the previously
verified genuine IBM path-time average. Nonconstancy of this particular sine
observable or nonzero divergence of every weighted direction is not proved here.

## Complete verification

All30 new public types and all293 final source/proof lines are read. Full bodies
of pairingFunction, correction, output, nativeField and the reused PairingResult
are printed and reviewed, including the actual projection, minus sign, total
contraction and original adjoint. Fresh complete root build, complete transitive
safe Foundation axiom audit, six independent Lean examples and pinned input
integrity checks are required. The tests cover the generalized value formula,
bounded-field criterion without gradient bounds, L4 criterion, concrete nonzero
native fields, actual sine-of-IBM-average observables, and actual predictable
stochastic-integral fields under the total-contraction condition.

Exact code, final timings, terminal results and hashes are in
STARDUST_IBM_NATIVE_INTEGRABLE_DIVERGENCE_VERIFICATION.json. Development repairs
were explicit Holder output exponents, factored integral identities, the existing
partialDerivative namespace and the actual memLp_congr_ae transport lemma.
No axiom, proof-resource, trust or toolchain change. All2170 previous
Foundation/root sources remain unchanged except three appended root imports;
three pinned configurations and all113 immutable manuscript paths/hashes are
checked. Source manuscripts remain untouched and uncommitted.

## Remaining actual IBM calculus

This extends native source-variable calculus on genuine IBM observables.
Observable projection remains explicit unless actual observable membership is
proved. It is not a physical-time IBM Itô/Tanaka formula and does not establish
temporal adaptedness, local time, bracket/versions, a universal causal
Clark–Ocone formula, or a maximal divergence multiplier domain. The process
time calculus and precise raw/germ comparisons remain open. Continue IBM before
the saved later campaigns; no change to the research queue or verification gates.
