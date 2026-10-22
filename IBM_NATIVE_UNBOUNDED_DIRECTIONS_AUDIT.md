# Checkpoint1345 — unbounded IBM directional multiplication and clock symmetry

Let u_{h,k} be checkpoint1344's actual deterministic native field with original
coefficient directions h (source) and k (clock). For EVERY f in FULL ORIGINAL
Dom(D), no value bound assumed, require the actual product

    f * delta(u_{h,k}) belongs to L2.

Then its genuine weighted field f*u_{h,k} belongs to ORIGINAL Dom(delta), with

    delta(f*u_{h,k}) = P_IBM (f*delta(u_{h,k}) - C_{h,k}(Df)).

The field is constructed as an actual continuous linear lift of scalar JointL2
into the ORIGINAL native field space. Its original coefficient representatives
are exactly f*h and f*k. The contraction is an actual continuous linear map
whose representative is the sum of the two original-coordinate inner products.
Both maps reuse fixed-direction continuous maps and the existing Lp action;
there is no unbounded multiplication operator silently defined on all fields.

`IBMNativeUnboundedDirections.unbounded_graph`, `unbounded_mem` and
`unbounded_value` prove the original graph, membership and exact value. The
complete `output` body retains the actual drift product and observable projection.
The drift-product condition remains explicit for general source/clock directions.

## Convergence and closure

Use the existing SAME-domain bounded sine clips of f. Their actual scalar values
converge strongly in JointL2 and their ORIGINAL native gradients converge strongly
in the native field Hilbert space. The directional lift and contraction maps
transport these limits continuously. Actual clipped products with the fixed
native divergence value converge STRONGLY in scalar L2 by dominated convergence,
using precisely the assumed L2 product f*delta(u), not an unjustified product of
two arbitrary L2 classes. The existing IBM observable projection transports the
output limit. The ORIGINAL divergence graph is closed, so the simultaneous
field/output limit proves original-domain membership and the stated value.

The new `drift` is the actual MemLp.toLp product under its supplied proof.
It agrees with the previous bounded multiplier when f is bounded; an independent
test verifies that the complete unbounded output agrees with the bounded output.
No pathwise, uniform-time or weak-only convergence replaces the strong L2 limits.

## A rigorous clock-sign connection

`IBMNativeClockDirection` computes the actual ambient partial divergence of a
deterministic direction from the existing first-chaos divergence graph. Native
unitary transport identifies its clock scalar as the actual clock lift of that
first-chaos variable. The verified clock-sign reflection fixes every IBM
observable and negates this first-chaos scalar. It is therefore orthogonal to
the ENTIRE observable space, and its full intrinsic projection is zero.

Consequently `nativeDrift_zero` proves delta(u_{0,k})=0. For k != 0 the native
field itself is nonzero (`clock_direction_ne_zero`), giving an explicit genuine
kernel direction of the original intrinsic divergence. No injectivity of fields
or universal clock innovation is assumed. This does not exclude the previously
proved nonzero observed EVEN-clock quadratic channels.

For EVERY f in full original Dom(D), including unbounded f, the drift-product
condition for u_{0,k} is now automatic and the actual value formula is

    delta(f*u_{0,k}) = P_IBM (-C_{0,k}(Df)).

The result does NOT assert that the right-hand side vanishes for every f.
An independent test instantiates this unconditional rule with the actual native
IBM time average for every T >= 0. Its full-domain membership and equality with
the genuine process time average are reused from verified foundations. No
membership of arbitrary point observations in Dom(D) is assumed.

## Verification contract

All32 new public types, FIVE complete actual definition bodies (lift, contract,
drift, nativeDrift, output) and all357 final source/proof lines are read. Fresh
complete root build, complete transitive safe Foundation axiom audit and six
independent Lean examples are required. The examples cover actual lift fields,
full unbounded graph scope, actual clipped drift convergence, nonzero pure-clock
kernel directions, the unconditional genuine IBM-average value formula, and
compatibility with the bounded output. Exact code, timings, counts and hashes
are recorded in STARDUST_IBM_NATIVE_UNBOUNDED_DIRECTIONS_VERIFICATION.json.

Development repairs were explicit coefficient-map representatives, coordinate
substitution before a.e. transitivity, factored contraction linearity, orientation
of image_iff, function-composition representatives under clock transport, and
explicit zero-subtype operator values. Failed target logs are retained. No new
axiom, trust, proof-resource or toolchain setting. All2173 prior Foundation/root
sources are unchanged except four appended imports; three pinned configurations
and all113 immutable manuscript paths/hashes are checked.

## Remaining scope

This extends genuine native source-variable calculus. General source-direction
drift integrability, physical-time IBM Itô/Tanaka/local-time formulas, actual
versions/bracket, raw/germ comparison and universal causal Clark–Ocone remain
open. The clock kernel result does not identify signed clock Brownian motion
as an observed IBM innovation. Preserve the earlier full initial-germ and
target-dependent-channel qualifications. IBM stays active; the linear campaign
queue and all verification/private-backup gates remain unchanged.
