# Intrinsic IBM absolute-value and arbitrary-level chain rule — checkpoint1340

For every f in the FULL ORIGINAL native joint derivative domain and every
real level a, the actual observable abs(f-a) belongs to the SAME domain.
Both original-coordinate gradient fields are sign(f-a) times the respective
original fields of Df, and norm(D(abs(f-a)))<=norm(Df). Sign is zero at zero.
This is proved without assuming that f has an atomless law or avoids a.

`IBMIntrinsicAbsoluteChain.absolute_chain` and `absolute_shift_chain` prove
these exact `ChainResult` specifications. The full definitions of that
specification, `GraphResult` and the new `RadiusResult` are printed in the
complete root audit and actually read. A named Prop never replaces reviewing
its actual domain, value, both gradient formulas and norm bound.

## Reuse and actual construction

The scalar functions sqrt(x^2+epsilon^2), x/sqrt(x^2+epsilon^2), their actual
derivatives, uniform value errors and slope bounds ALREADY exist in
`SmoothAbsoluteApproximation`. `BrownianTanakaApproximation.slope_tendsto_sign`
proves the scalar limit at EVERY real x, including x=0. Only those scalar
facts are reused. No Brownian martingale, Brownian local time or Brownian
predictable integral is identified with an IBM object.

The1339 unbounded C1 native graph construction supplies actual radius outputs
in the existing IBM derivative domain, with both native section fields.
`radius_value_limit` uses the uniform scalar error and the actual probability
law to prove strong JointL2 convergence to the genuine absolute-value class.
`radius_gradient_limit` invokes the previously verified bounded native
multiplier convergence, retaining actual coefficient-valued product L2 fields.
Both gradients converge strongly to their true sign multipliers. Pointwise
slope convergence holds at zero, so no null-probability assumption is needed.

`absolute_graph` passes these actual limits through the ORIGINAL closed joint
derivative via the1339 `close_graph` theorem. The result uses the same
observable Hilbert space, domain, two native channels and Hilbert adjoint.
The1339 graph packaging and1338 coordinate-flip/energy calculation give both
ORIGINAL-coordinate formulas and the contraction bound.

Arbitrary levels use the actual original-domain constant-one element and its
verified zero derivative. `shifted_value` identifies f-a*1 with the actual
representative f-a; `shifted_derivative` proves D(f-a*1)=Df. Applying the proved
absolute-value rule gives the full arbitrary-level result, including atoms at a.
No new Gaussian, measure, closure operator or stochastic integral is introduced.

## Precise contribution and limits

This is a nonsmooth SOURCE-variable Malliavin-type absolute-value rule for
actual IBM observables. It supports native nonlinear integration by parts and
the existing target-indexed ACTUAL stochastic reconstruction. The latter still
retains the whole initial germ and uses a channel depending on the target.
It does not establish physical-time IBM Tanaka/local-time identities, an
occupation-density theorem, a universal noise or causal Clark–Ocone.
Point IBM observations are not assumed to lie in Dom(D).

The native smooth-radius values and BOTH actual gradient fields converge
strongly in their respective L2 spaces; verified unitary transport and finite
channel assembly give the Hilbert graph limit used by closedness. No pathwise
or uniform-in-time convergence is inferred. A local-time correction is not
manufactured from this source derivative formula.

Independent tests cover full-domain absolute value, all real levels, a constant
input with a purely atomic law and zero gradient, simultaneous actual value
and source/clock L2 limits, and arbitrary-level absolute output's actual native
stochastic IBP plus1337 target-indexed reconstruction. Physical-time versions,
bracket, causal-gradient/noise identification, raw/germ comparison and the full
intrinsic IBM calculus remain open. Focused F1–F3 exact-domain results stand.

## Verification contract

Two modules,178 final source/proof lines,12 public declarations. The fresh full
root build passed6331 jobs in28.235s. Complete transitive safe-Foundation audit,
all unabridged public types and the three complete result-specification bodies,
final source/proof review and five independent tests are recorded in the
verification JSON. All2160 prior mathematical sources are unchanged except two
appended root imports; three configurations and113 archive paths/hashes are
checked unchanged. The only development repair to date made the norm-to-absolute
representative identity explicit. No new proof-resource or trust override.
Failed development logs are retained; only final successful gates certify work.
Explicit Git commit, exact-commit receipt and verified PRIVATE main/research
synchronization remain mandatory. IBM and the indefinite goal stay active.
