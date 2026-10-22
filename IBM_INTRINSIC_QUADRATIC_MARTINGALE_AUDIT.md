# Actual IBM quadratic martingale — checkpoint1307

IBM remains ACTIVE. This checkpoint constructs a genuine nonzero square-integrable
martingale in the raw natural filtration of the constructed continuous IBM process.
It does not complete intrinsic IBM stochastic calculus or change the campaign queue.

Write Z_t=X(|Y_t|), with the existing independent constructed continuous Gaussian
scenery X and Brownian clock Y, under IBMSourceLaws.jointMeasure. Write F_t for
IBMNaturalFiltrationObstruction.naturalFiltration t. All times are nonnegative.

## Exact construction and domains

IBMIntrinsicQuadraticMartingale.value t is the actual scalar conditional expectation
M_t=E[Y_t^2-t | F_t]. Its valueClass is the corresponding element of the existing
closed L2 past space. The valueClass_ae bridge identifies the actual function with
that Hilbert projection. value_memLp proves square integrability for every time.
actual_martingale proves the full Mathlib Martingale predicate in F, with actual
strong adaptation and conditional consistency for every s<=t. value_zero proves
M_0=0 almost surely. value_nonzero proves M_t is not almost surely zero at every
t>0. valueClass_bound_sq proves ||M_t||_2^2 <= 2t^2.

The construction reuses the verified Gaussian second Hermite martingale and its
exact L2 norm. No new stochastic law, Gaussian innovation, or hypothetical process
is assumed. The raw IBM process Z itself remains subject to the earlier verified
nonmartingale obstruction.

## Conditioning and actual continuous versions

IndependentInitialConditioning.conditional_snd proves conditioning in the product
sigma algebra mX.prod n leaves a clock-only conditional expectation unchanged,
with both measures explicitly probabilities and f,g integrable. Its proof checks
rectangles and extends the integral identity to every product-measurable set by
pi-lambda induction. This is an independence theorem under the actual product law.

IBMClockInitialEnlargement.rawEnlargement knows full scenery initially and the
raw clock natural past at time t. The second Hermite process is a martingale
there by the preceding product conditioning identity. The actual continuous
clock version agrees with it at each time almost surely. Existing
AmbientMartingaleModification transfers it to the auxiliary enlargement obtained
by AmbientNullAugmentation. That construction adds only ambient-measurable events
having a raw measurable version almost surely. It is not a claim of full usual
completion or right continuity.

The actual IBM coordinate is measurable in this auxiliary augmented filtration:
first prove raw almost-sure measurability using scenery evaluation and the raw
clock, then apply the existing augmentation lemma. Consequently the ACTUAL RAW
IBM natural filtration is a subfiltration. It is not replaced or augmented.
Two applications of the conditional-expectation tower property now prove the
martingale identity for M in precisely the target filtration F.

## Nontriviality test against an actual observation

IBMActualQuarticMoment proves, by the actual scenery first-chaos representation,
E_X[Z_t^4]=3Y_t^2 and E_X[Z_t^8]=105Y_t^4, with the clock held fixed. The eighth
power is jointly integrable by actual product integration and clock moments;
Z_t^4 therefore defines fourthClass t in L2, measurably in F_T whenever t<=T.
These are actual process classes, not replacement polynomial variables.

IBMEvenClockProjection.quadratic_fourth_pairing proves

    <Y_t^2-t, Z_t^4>_L2 = 6t^2.

All product integrability, Fubini and clock second/fourth moment steps are proved.
Orthogonal projection against fourthClass t preserves this nonzero pairing.
conditional_quadratic_ne_zero therefore proves E[Y_t^2-t | F_T] is nonzero
for every 0<t<=T, and value_nonzero specializes T=t.

This complements checkpoint1306: E[Y_t | F_T]=0 for every t,T by global clock-sign
symmetry, but the EVEN quadratic channel survives. Blackness or a signed-clock
obstruction cannot be used to infer absence of all natural martingales.

## Remaining obligations and next productive step

No path continuity or right-continuous modification of M, quadratic variation,
Brownian law, independent increments, predictable representation property,
or general intrinsic Clark-Ocone formula is established here. Nonzero M alone
does not prove it spans the IBM filtration or represents arbitrary observables.
Nor does it identify Y_t^2-t itself as F_t-measurable: the result is its conditional
projection. All-time observable density and the verified past derivative/adjoint
calculus remain available but do not supply temporal predictability automatically.

Next investigate genuine predictable step integration against this constructed
martingale and its L2 control, reusing the existing finite-grid integral machinery.
Connect actual adapted increments and their orthogonality to the native operator
calculus before asserting any completed temporal representation. Preserve the
F1/F2 correction terms and clock-number smoothing in their proven domains.

## Verification contract

Five modules, 411 source lines and 39 public declarations. The checkpoint requires
the complete root build, complete transitive safe-Foundation axiom audit (only
propext, Classical.choice and Quot.sound), actual unabridged type/proof review,
four independent Lean tests, all prior source/configuration identities and all
113 manuscript paths/hashes. Exact observed results and reproducible test source
are recorded in STARDUST_IBM_QUADRATIC_MARTINGALE_VERIFICATION.json after those
checks terminate. No new proof-resource or trust override is introduced.
Git commitment and exact-receipt PRIVATE main/research synchronization are
separate final gates; this audit document alone certifies neither gate.
