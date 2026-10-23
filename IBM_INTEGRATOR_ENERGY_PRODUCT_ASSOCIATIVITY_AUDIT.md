# IBM checkpoint1373: change of integrator and actual associativity

IBM remains ACTIVE and incomplete. This checkpoint closes the general bounded
predictable-action identification left open at1372. It also proves literal
product-domain associativity on the entire original output-channel L2 domain.
No manuscript is edited and no novelty claim is made.

## Original objects and exact domains

Use the existing joint-source probability space, original raw-natural-past
predictable sigma algebra, original predictable energy measures mu_F, and the
existing actual stochastic isometries I_F. Given an original channel F and
H in the entire original random predictable L2(mu_F), put Y=I_F(H).

`IBMStochasticIntegratorEnergy.energy_change` proves equality of measures on
the ENTIRE original predictable sigma algebra:

    mu_Y = mu_F.withDensity(ofReal(H^2)).

H denotes the actual strongly measurable Lp representative. Finite measure,
origin zero, and equality on adapted rectangles are proved. Rectangle equality
uses the actual1372 stochastic pull-out identity and original stochastic-step
energy. Existing finite-partition and signed-measure uniqueness results then
extend equality to the full sigma algebra. This is not merely an equality of
expectations, total masses, rectangle tests or formal quadratic forms.

## Literal products and unbounded integrands

For EVERY K in the entire ORIGINAL random predictable L2(mu_Y),
`IBMStochasticProductAssociativity.product_memLp` proves H*K belongs to
L2(mu_F). `product_ae` identifies its actual representative. `weighted_ae`
handles the different null ideals correctly: equality mu_Y-AE implies equality
of the H-weighted products mu_F-AE, including the locus H=0. Reverse absolute
continuity of the two measures is neither needed nor asserted.

`productIsometry` is a genuine linear isometry L2(mu_Y) -> L2(mu_F), with
literal product representative and exact norm equality. `actual_associativity`
proves the stochastic identity on this ENTIRE domain:

    I_F(H*K) = I_(I_F H)(K).

The proof identifies original predictable cells using1372 and extends by the
existing original dictionary density. No boundedness of K, finite grid or
finite chaos restriction is introduced. Norm-convergent L2(mu_Y) approximations
converge in original L2(mu_F) after multiplication and in actual source L2
after stochastic integration. Arbitrary products of unrelated L2 functions
are not claimed integrable; the precise output-energy domain is essential.

## Every completed family and every bounded predictable action

For any family F_i and any z in its EXISTING signed-covariance completion,
write J_F for the existing actual completed stochastic isometry and Y=J_F z.
For EVERY original raw-predictable globally pointwise bounded real function g,
`IBMCompletedBoundedAssociativity.actual_bounded_associativity` proves

    J_F(M_g z) = I_Y(class_mu_Y(g)).

`nested_identification` proves equality in the completed input space itself:

    M_g z = nestedIntegral(F,z,class_mu_Y(g)).

Thus the prior1371 bounded action is identified with the ORIGINAL actual
stochastic integral throughout the completed domain. The open identification
recorded at1372 is CLOSED here, not retroactively erased from that record.

The proof appends one original channel G to the family via Option indices.
The already verified full signed joint multiplier bound yields a comparison
inequality between ANY completed output and ANY single original integral.
Existing terminal self-representation and completed remainder membership
discharge existence of a single original stochastic representation of Y.
Equal actual outputs force equal g-modified outputs. Single-channel literal
product associativity identifies the latter with I_Y(g). No new conditional
representation premise, PVM, monotone-class calculus or replacement integral
is introduced. The SAME g acts on every channel. Arbitrary channel-dependent
g_i and globally bounded actions for arbitrary unbounded g are not asserted.

## Verification and remaining frontier

Three new modules: energy108lines/9public; product182lines/17public;
completed114lines/8public. Total404source/proof lines and34public declarations.
Fresh root build6406jobs passed; complete transitive safe Foundation audit
42664declarations passed with only propext, Classical.choice and Quot.sound.
All final source/proof lines, all unabridged new public types, and twelve printed
old/new definitions were actually read. Eight independent Lean examples passed:
full measure equality; literal product domain/AE/norm; full-domain associativity;
arbitrary completed identification; equal-output comparison; nonzero actual
IBM1 reconstruction with nonzero product input; zero integrator; and genuine
L2 convergence of products and actual stochastic outputs.

The first independent run failed only on reducing the zero-function coercion
in the zero-integrator test. Explicit Pi.zero_apply closes that same test at
unchanged defaults. All eight scratch development logs and exact failed test
code/log/time are retained. No resource limits, trust or checks were changed.
The verification JSON records exact timings and all source/configuration hashes.
All113 archive paths and hashes remain identical to inventory1292.

This establishes substantial actual stochastic integration laws. Full IBM
calculus is still OPEN. In particular, predictable energy measure equality
alone does not construct pathwise quadratic variation, a pathwise bracket or
a cadlag modification. The martingale P_t Y associated with a fixed terminal
observable is distinct from the uncorrected IBM path, which remains subject
to the verified nonmartingale obstruction. Physical-time Ito/Tanaka identities,
intrinsic closure/chain rules and temporal-gradient Malliavin Clark–Ocone
still require their own exact theorems and domains. Ordinary point-DomD
obstructions remain. No queued campaign is activated by this checkpoint.
