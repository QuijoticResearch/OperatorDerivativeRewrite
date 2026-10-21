# Final higher-heat multichannel campaign

The A(2) stopping commit `3f30ef6e33e6a2954be7f5afd1b461068f701ca1` passed
its exact receipt and verified PRIVATE main/research refs before this campaign
opened. A(4), integer/conditional-real and A(2) investigations are frozen.
This is the final queued attempt; October 31, 2026 is the hard stopping date.
There is no subsequent research campaign.

## Checkpoint 1277: actual third biharmonic signed step channel

Reuse starts from the signed analytic completion, actual bounded pairing,
all-time cutoff derivatives, L1 weak transpose, completed first/second signed
step identification and adapted closure. No finite signed path measure for
all higher-heat marginals is introduced. The finite signed laws and their
compatible polynomial cylinder algebra remain the actual source of expectations.

For physical order p=4 (m=2), positive horizon T and normalized time [0,1],
`HigherHeatThirdChannelSteps.thirdChannel` is the bounded map

```
I3 = 6 * coefficient(2,T) * transpose(timeMeasure,1)
   = -24*T * transpose(timeMeasure,1).
```

Its fields are the same genuine L1(time;Domain*) fields as the other channels;
its target is the same completed analytic test dual. This construction is
not itself identification with a limit of native cubic sums.

Let B_j(F) be the existing actual dual coefficient step field on cell j,
D_j the derivative in its increment coordinate, and J the existing actual
signed density pairing into Domain*. The new theorem is

```
J(F * deltaX_j) = I1(B_j(F)) + I2(B_j(D_j F))
                   + (1/2)*I3(B_j(D_j^2 F)),  when D_j^3 F = 0.
```

`native_quadratic_agreement` proves the actual signed-moment identity first.
`derivative_iterate_step` and `quadraticCorrection_split` preserve every
coefficient under refinement. `quadratic_agreement_finer` proves agreement
with EVERY polynomial probe on EVERY finer grid. Density and boundedness
then give `quadratic_agreement_dual` on the WHOLE completed test domain.
The factor 1/2 is essential; this is the third product-Leibniz coefficient,
not a guess from a positive stochastic isometry.

For F missing the current increment coordinate, the resulting exact identity is

```
J(F * deltaX_j^3) = I1(B_j(F * deltaX_j^2))
                    + 2*I2(B_j(F * deltaX_j)) + I3(B_j(F)).
```

`HigherHeatCubicStepIdentity.cubic_step_dual` proves this as an equality of
continuous functionals; `cubic_step_actual` identifies its polynomial probes
with the ACTUAL finite signed-kernel cylinder expectation. The assumption is
precisely j not in F.vars; a genuinely past-adapted F is a special case.
No adaptedness is falsely assigned to the correction fields containing the
CURRENT increment. Their disappearance after summing/refining remains a
separate norm estimate and limit obligation.

The independent signed-moment tests check the coefficient against all three
monomial coefficient degrees 0,1,2 and sixteen probe degrees at four exact
rational time scales. They also check the cubic identity

```
E[deltaX^3 G] = -24*h E[G'] + 144*h^2 E[G^(5)] - 64*h^3 E[G^(9)].
```

This is an independent normalization test, not a substitute for the actual
signed-kernel proofs. The Lean tests retain the centered terminal-cubic
one-/two-channel obstruction and test the new channel's nonzero linear probe.
They do not assert that the entire terminal cubic is the third channel alone.

## Exact next obligations

1. Bound the anticipating cubic corrections in dual norm, using the existing
   completed quadratic identity and first/second step bounds. For mesh d and
   a uniform actual coefficient dual-norm bound M, the candidate summed bound
   is `(144*T^2*d + 64*T^3*d^2)*M`. This bound and its limit are NOT YET
   Lean-certified at 1277; the exact signed moment computation suggests it.
2. Prove convergence of actual native cubic sums to I3 on genuine convergent
   L1 adapted coefficient fields. The hypotheses must include the actual
   uniform bound and field convergence, or prove them for the concrete fields.
3. Construct the needed quadratic predictable coefficient field from existing
   dual continuity/polynomial estimates and prove its genuine L1 approximation.
   Then test the actual terminal cubic reconstruction using all three channels.
4. Generalize the correct complementary hierarchy to p-1 channels, with the
   appropriate factorial/Leibniz coefficients, actual signed sum identification,
   causal coefficient domains and a proved convergence topology.
5. Extend reconstruction to the completed analytic domain only after the
   corresponding boundedness, density and causal approximation hypotheses are
   established. Do not replace it with a finite complex-noise or finite-grid
   statement, and do not infer impossibility from missing one/two channels.

Universal completed multichannel Clark-Ocone, the general nonlinear drift
formula, general tensor causal projection and unquotiented integrand
injectivity remain open. The original manuscript is unmodified, including
SHA256 `52671C5A5A77C892CEB8AFC183C7BFBA1520BF0EB3BA1A0E60AE0403063CC6C7`.
Its false positive norm/isometry and D^p-only claims are not reinstated.
All full-build, transitive axiom, unabridged type/proof, source-integrity,
research-ledger and exact PRIVATE backup gates remain mandatory.
