# Selective audit: renormalized Airy integration by parts

October 21, 2026, checkpoint 1292. This supports the active multichannel
pseudoprocess campaign. It does not open an odd-order/KPZ research campaign or
advance IBM prematurely. No novelty claim is made.

Source: `ResearchSources/Incoming/renormalized_airy_ibp.tex`, title **Regulated
observables for higher-order heat pseudo-processes: renormalized Stein
identities, covariance formulas, and Airy threshold sensitivities**. SHA256:
`6012E74DF2B4178DEE3091815A7062F7AC5B7E1B25A60438A32F40FFFB7E12FB`.
The manuscript is preserved read-only. Its statements are research claims,
not instructions or verified dependencies. The exact archive inventory is
`STARDUST_RESEARCH_SOURCE_INVENTORY_1292.json`: 113 files, all 112 files from
checkpoint 1290 unchanged, plus the already hash-recorded Airy arrival.

## Main assessment

| Source claim | Assessment and exact boundary |
|---|---|
| Lemma `lem:tail`, regulated g with g' Schwartz | Sound tail argument: integrate a sufficiently strong Schwartz bound for g'. The N=0 case uses integrability or a stronger bound, not an integral of (1+abs(x))^-1. |
| Theorem `thm:bridge`, subtraction of the oscillatory-side limit | The repeated finite-interval integration-by-parts argument is valid PROVIDED the stated kernel ODE, polynomial derivative bounds on the oscillatory side, and derivative decay on the other side have been established for the chosen kernel. Both bulk integrals are then absolutely convergent and each boundary product tends to zero. This is a justified conditional mathematical repair, not a new Lean construction of all odd-order kernels. |
| Airy corollary `cor:airy` | The classical Airy ODE and asymptotics supply these analytic inputs. The subtraction removes the undifferentiated boundary value; it does not construct stochastic integration or Clark–Ocone. |
| Input I2 and Pascal defect `prop:carre` | Algebraic Stein and iterated Leibniz identities have direct verified counterparts, listed below. The even-order sign must be dissipative. |
| Input I3, single-channel Itô-p | Cannot be imported. The actual signed calculus requires higher stochastic channels. Existing quartic centered-cubic and first-channel-range obstructions already show why a Brownian-style single-channel reduction is insufficient. The manuscript states I3 for bounded tests; polynomial obstructions alone are not literally counterexamples within that stated class. A bounded-test extension must specify its domain and topology and confront the same missing channel structure. |
| Covariance `thm:debruijn`, `thm:twotime` | The generator product-defect mechanism is correct. The stated regulated-class theorem still requires a well-defined extension of the semigroup/pairings, uniform time estimates including endpoints, and justified differentiation/integration. Its proof via I3 is not verified. A semigroup proof can avoid I3 entirely. The precise actual signed Fourier specialization is now proved in Lean. |
| Graded reconstruction `eq:graded-co` and `prop:isometry` | Not established by the text. The projection, p-fold chronological integral, normalization, domain and topology require definitions and proofs. Defining the integrand pairing as E[delta(Y)delta(Y')] makes the displayed covariance equality a consequence of the ASSUMED reconstruction, not independent evidence for it. Neither positive isometry nor integrand uniqueness follows. The existing universal D^p obstruction uses a linear witness outside the p-graded class; it must NOT be misrepresented as refuting the restricted graded claim. That restricted claim remains unverified. |
| Airy kernel intertwining `lem:airykernel` | Correct under differentiated-integral domination: the Airy ODE cancels the shared spectral parameter. This is a connection of deterministic operators, not identification of the signed Airy propagator law with a positive Airy-sheet/Tracy–Widom law. |
| Conditional Fredholm Ward statement `prop:conditional` | No precise resulting equation or uniform limiting estimate is supplied. Trace-class C1 differentiability does not supply second differentiability, nor eliminate determinant chain-rule/resolvent terms. Airy equations for entries alone do not give an Airy equation for the determinant. Keep this open; it supplies no current stochastic theorem. |

## Normalization and analytic corrections

With the manuscript's characteristic convention E[exp(ikX_t)] = exp(c(ik)^p t),
the BACKWARD generator on observables is c d^p/dx^p, while the FORWARD kernel
equation is d_t K = (-1)^p c d_x^p K. The introductory identification of that
characteristic function with the forward equation d_t K = c d_x^p K needs an
odd-order sign correction. Its Airy example confirms this directly: for
K(t,x) = t^(-1/3) Ai(x t^(-1/3)), the Airy ODE gives
d_t K = -(1/3) d_x^3 K. Its characteristic function and backward coefficient
c3=1/3 are consistent with each other; the forward PDE sign is the error.

For even p=2m, a tempered dissipative kernel requires c*(-1)^m < 0. The
manuscript initially permits every nonzero c and supplies this restriction only
later. An example excluded by the necessary restriction is p=4, c=+1: the
proposed characteristic multiplier exp(t*k^4) is unbounded and is not the
Fourier transform of a finite signed kernel. Stardust uses c=(-1)^(m+1).

The Airy function itself has a DECAYING oscillatory envelope of order
abs(x)^(-1/4), while its first derivative has envelope abs(x)^(1/4). Thus
"non-decaying/growing kernel envelope" is inaccurate for K itself; the weighted
kernel and boundary derivatives are the relevant obstruction. Authoritative
inputs: [DLMF Airy equation](https://dlmf.nist.gov/9.2.E1),
[DLMF asymptotic expansions](https://dlmf.nist.gov/9.7), particularly 9.7.9–10.
These external analytic inputs are not asserted to have been formalized here.

The hard-threshold tail integral from a to infinity is absolutely convergent
for every finite a, even when a is negative: the oscillatory portion is then
a bounded interval. Saying its support lies on the decay half-line is literally
false for a<0, but is not an obstruction to this integral. Passing a family of
smoothed thresholds to the hard limit still needs uniform domination; pointwise
convergence alone is insufficient.

For a concrete warning about determinant inference, let A solve A''=s*A and
consider the finite-rank trace-class family K(s)=A(s)*I on a two-dimensional
space. Then Q=det(I-K)=(1-A)^2, and
Q''-s*(Q-1)=2*(A')^2+s*A^2, generally nonzero. Even smooth entrywise Airy
equations do not remove the determinant's extra terms. This tests a naive
scalar Ward inference, not an unstated precise formula for a singled-out slot.

## Exact reuse and new verified connection

- `PseudoPolynomialStein.polynomial_stein`: the polynomial Stein functional for
  every p; odd p here is an algebraic moment functional, not an absolutely
  integrable signed kernel realization.
- `PureOrderPolynomialTransport.transport_eval`, `transport_add`,
  `transport_iterate_derivative`, `actual_kernel_transport`: exact polynomial
  evolution and actual even-order kernel agreement.
- `HigherHeatIteratedLeibniz.derivative_iterate_mul`: all Pascal channels.
- `HigherHeatFourierBracket.real_covariance_hasDerivAt`, `fourth_order_rate`,
  `fourth_order_not_quadratic`: the infinitesimal resonance defect and failure
  of a Brownian quadratic product correction.
- `HigherHeatFourierCovariance.kernel_product_integrable`, `kernel_product`:
  actual absolutely integrable signed-kernel Fourier covariance.
- `HigherHeatFourierProduct.conditional_product_defect`: exact finite-step
  product compensator under the actual signed transition.
- `HigherHeatAllProductChannels.agreement_dual`: finite product corrections on
  the whole completed analytic test dual.
- `HigherHeatFirstChannelRange.no_firstChannel_representation`: rigorous
  centered-polynomial range obstruction for the constructed first channel.
- `HigherHeatMultitimePredictableFields.field_tendsto`, `field_mem`,
  `field_bound`: actual multitime coefficient convergence and adapted membership.

NEW `HigherHeatResonanceCovariance.covariance_integral` integrates the existing
resonance slope exactly. Set w(x)=(2*pi*x)^(2m),
R=w(xi)+w(eta)-w(xi+eta). For every real T,

    exp(-T*w(xi+eta))-exp(-T*w(xi))*exp(-T*w(eta))
      = integral_0^T R*exp(-t*w(xi+eta)-(T-t)*(w(xi)+w(eta))) dt.

`actual_kernel_covariance` identifies this time integral with the actual
signed-kernel integral of the product of the two Fourier innovations for m>0,
T>0. `density_continuous` proves time integrability; `fourth_order_density`
exhibits the complete 4,6,4 cross-channel resonance. The proof uses the existing
kernel identity and the fundamental theorem of calculus. It assumes neither
a path measure nor any stochastic Itô/Clark–Ocone formula. This is an exact
Fourier covariance identity, not completion of signed stochastic reconstruction.

Independent Fraction arithmetic tests check 2,704 monomial covariance identities
for p=2,...,9, both coefficient signs, degrees 0,...,12, and rational horizons.
They recover the manuscript's coefficients 324 for the cubic square and
19,828,800 for the sixth-power square at p=3. Odd-order tests are finite formal
moments only. Reproducible code/results are retained with checkpoint verification.

## Regulated tests are not automatically in the existing completion

`MultivariateFactorialDomain.polynomial` weights a degree-n Taylor coefficient
by n!, with l1 summability. Already on the one-time one-coordinate subspace,
the normal CDF Phi has Taylor derivative magnitudes at zero

    abs(Phi^(2n+1)(0)) = (2n)!/(2^n*n!*sqrt(2*pi)).

The unscaled factors have successive ratio 2n+1 and never tend to zero; their
sum diverges. Thus its natural Taylor series is not a convergent factorial-l1
series in this domain. The same divergence persists under any fixed positive
rescaling of the coordinate, since the ratio gains only a fixed square factor.
This rules out the straightforward Taylor-completion identification; it does
not assert that every conceivable alternative realization is impossible.
Smoothness, boundedness and Schwartz derivatives alone cannot justify importing
the manuscript's entire Reg class into the existing analytic calculus.

## What remains active

This source offers a useful operator/covariance cross-check and a carefully
conditioned odd-order boundary repair. It does not discharge current full
multitime (p-1)-channel Clark–Ocone reconstruction, cofinal consistency/linearity,
completed OBSERVABLE extension, or chronological tensor uniqueness. Continue
those obligations using checkpoint 1290. Do not replace actual signed identities
with expectation-only formulas, or build a new threshold/KPZ infrastructure
merely to ingest this manuscript. Full builds, transitive axiom audits,
unabridged type/proof reviews, source hashes and private backup remain mandatory.
