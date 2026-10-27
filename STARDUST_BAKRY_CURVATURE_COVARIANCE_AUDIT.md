# Bakry Objective2 — curvature/covariance audit

## Checkpoint1622: sharp positivity on the entire physical Haar-L² cone

`Foundation/PhysicalHeatPositiveCone.lean` extends 1621 from finite Fourier
squares to **every** almost-everywhere real nonnegative element of the
completed Haar-L² space on the three-torus. The exact
`torusSynthesis_mul`/`torusSynthesis_reflection` identities identify the
algebraic square `reflection f * f` with `|torusSynthesis f|²` pointwise.
Mathlib's dense multivariate Fourier span in continuous functions, followed
by a continuous square root, proves each continuous nonnegative function
lies in the uniform closure of these finite squares. The continuous map
from continuous functions to Haar L² transfers this closure. A 1-Lipschitz
complex-to-nonnegative-real clipping map commutes with that L² embedding;
density of continuous functions in L² then proves `positive_l2_square_closure`:
the finite square cone is dense in the **entire** nonnegative real L² cone.

The closedness argument uses the fixed-point set of the continuous L²
clipping map, not an unproved pointwise-limit claim. Combining it with
the existing exact semigroup/core intertwining and 1621 square positivity
gives `physical_evolution_positive_all`: any nonnegative rate satisfying
the verified finite covariance condition yields a positivity-preserving
completed physical L² semigroup at every nonnegative time. For mixed stable
rates, `anisotropic_physical_positive_iff_active` proves the exact criterion
`∀j, a_j>0 → γ_j≤2` under `a_j≥0, γ_j>0`. The reverse direction is the
explicit 1621 positive-measure negative-output square, so it tests the
entire-L² claim with an actual L² input. Inactive coordinates may have
arbitrary positive exponent. `anisotropic_stationary_constant` proves
zero-mode conservation; with the previously verified contraction, semigroup
law and strong continuity this gives a conservative positivity-preserving
contraction semigroup on the physical L² space under the active-axis
criterion. This is an operator theorem, not a constructed stochastic path
process or a Bakry–Émery curvature/entropy inequality.

Five new independent Lean tests exercise arbitrary positive L² data with
an inactive superquadratic coordinate, both directions of the exact
positive-cone closure equivalence, failure for an active superquadratic
coordinate, and constant preservation. Together with the five retained
1621 tests they check both new directions.
The proof uses the classical Fourier density theorem already in Mathlib;
no novelty claim is made. Next investigate whether this positive L²
semigroup admits a positive convolution kernel/probability transition law
and which additional regularity or tightness is required for a genuine
Lévy process. Graph-domain Γ, CD, entropy and LSI remain open.

Full root build: 6872 jobs, 27.138 seconds. Complete transitive
safe-declaration axiom audit: 52090 declarations, 44.650 seconds, using
only `propext`, `Classical.choice`, and `Quot.sound`. All 21 public types,
18 proofs, 3 definitions, 3 local instances and 10 independent examples
were reviewed; the independent Lean pass took 28.949 seconds. The final
source/config/archive hash and exact-commit receipt are recorded in the
checkpoint verification evidence. ResearchSources was not modified.

## Checkpoint1621: completed physical torus square positivity and failure

`Foundation/PhysicalHeatSquareBridge.lean` closes the finite-to-physical
identification left open at1620. `lift_heatAction` proves exact intertwining:
lifting the algebraic multiplier `exp(−t r(k))` on a finite Fourier
polynomial gives the **already completed Haar-L² torus semigroup** applied
to its lift. The proof compares every Mathlib torus Fourier coefficient.
`torusSynthesis_toLp` identifies each finite polynomial lift with the L²
class of its actual continuous trigonometric representative. This uses the
correct unit-torus normalization; the earlier period-`2π` box model is not
silently identified with it.

The pointwise torus identity `torus_heat_square_energy` realizes the
semigroup image of every finite Fourier square as the complex energy of
the finite exponential matrix. Under `CovarianceSymbol`,
`physical_evolution_square_ae` proves the genuine L² output is real and
nonnegative almost everywhere. `physical_square_input_ae` independently
proves the input itself is real and nonnegative almost everywhere.

The converse is physical too. A positive three-frequency symbol energy
gives a continuous heat image negative at the torus identity. Continuity
and positivity of Haar measure on nonempty open sets show the image is
negative on a set of **positive measure**, so the L² output fails
almost-everywhere nonnegativity. For the mixed stable symbol
`ψ(k)=∑_j a_j|k_j|^γ_j`, under `a_j≥0` and `γ_j>0`,
`anisotropic_physical_square_positive_iff_active` proves that the completed
semigroup preserves almost-everywhere nonnegativity of **every lifted
finite Fourier square at every nonnegative time** if and only if every
positive-weight axis has exponent at most two.

For any active `γ_j>2`, frequencies `(0,1,2)` on axis `j` and weights
`(1,−2,1)` give a nonnegative L² square whose semigroup image is negative
on a positive-measure set at some positive time. Zero-weight
superquadratic coordinates remain harmless. This is the classical
Schoenberg/Bochner threshold transported through the actual physical
semigroup; no novelty claim is made. The original Schoenberg source is
cited in checkpoint1619 below. Mathlib's `UnitAddTorus.mFourierBasis`,
`ContinuousMap.toLp`, and open-positive Haar measure supply the physical
realization.

The theorem covers the **square core**. Positivity preservation for every
nonnegative element of the completed real L² cone requires a separate
density/closure argument for positive squares, including L⁴ approximation
and product convergence. No convolution probability kernel, Lévy process,
Bakry CD/LSI inequality, or Yang–Mills implication follows. Objective2
remains active; the manuscript archive is unchanged.

Verification: complete6871-job incremental root build, full52057-declaration
transitive axiom audit with only `propext`, `Classical.choice` and
`Quot.sound`; all17 public types,16 complete proofs,1 definition,3 local
instances and5 independent Lean checks reviewed. Source2691/config3/
archive113 hashes match the exact checkpoint baseline and manuscript
inventory. Final-source full build25.71s, audit44.10s,
independent checks35.94s.
The exact Git receipt and guarded PRIVATE backup follow; this does not
close Objective2.

## Checkpoint1620: finite Fourier heat squares and the sharp obstruction

`Foundation/FiniteHeatSquarePositivity.lean` defines the finite Fourier
diagonal heat action with mode multiplier `exp(−tψ(k))`. The exact
`heat_square_energy` identity identifies its physical synthesis on an
algebraic square `reflection f * f` with the complex quadratic energy of
the finite Schoenberg matrix. Thus, for every covariance symbol, every
`t≥0`, every finite Fourier polynomial and every spatial point,
`heat_square_nonnegative` proves that the heat image of the square is real
and nonnegative. This is a genuine pointwise trigonometric-polynomial
statement, strengthening checkpoint1619's matrix assertion on the finite
core; it reuses the previously verified reflection, synthesis, complex
energy and finite Schoenberg theorems.

The converse failure is equally concrete. At the spatial origin, real
coefficients identify the heat-square value with the exponential matrix
energy. A positive conditional-negative-type violation on a three-frequency
zero-sum vector therefore yields a **negative pointwise heat image** at
some positive time. For the mixed stable symbol with `a_j≥0`, `γ_j>0`,
every positive-weight coordinate above exponent two has the explicit
three-frequency polynomial with coefficients `(1,−2,1)` whose square becomes
negative under the finite heat action. Under the exact active-axis condition
`a_j>0 → γ_j≤2`, all finite Fourier squares have nonnegative heat images.
The zero-weight superquadratic exception remains valid. These are standard
Fourier/Schoenberg consequences, not a novelty claim.

The finite algebraic heat action is not yet identified with a positivity-
preserving extension of the completed Haar-L² semigroup. The theorem does
not supply a convolution probability measure, Lévy process, pointwise
positivity for every nonnegative trigonometric polynomial via a verified
sum-of-squares theorem, a Markov kernel, or a Bakry curvature/entropy bound.
The physical torus/core bridge and exact completed generator domain are
separate verified results; the positivity transfer beyond squares remains
open. Original manuscripts remain byte-for-byte unchanged.

Verification: complete6870-job incremental root build, full52028-declaration
transitive axiom audit with only `propext`, `Classical.choice` and
`Quot.sound`; all9 public types,8 complete proofs,1 definition and5
independent Lean checks reviewed. Source2690/config3/archive113 hashes match
the exact baseline and manuscript inventory. Final-source full build41.42s,
audit59.35s, independent checks34.21s. Exact Git commit, receipt and guarded PRIVATE
backup follow; this is not an Objective2 stopping checkpoint.

## Checkpoint1619: finite Schoenberg equivalence and exact heat threshold

`Foundation/FiniteSchoenberg.lean` proves a complete finite-matrix bridge for
real Fourier symbols. `entrywise_exp_psd` takes an arbitrary finite real PSD
matrix to its entrywise exponential: Schur powers and nonnegative factorial
coefficients give PSD partial sums, and the closed PSD cone admits their
entrywise exponential-series limit. `heat_multiplier_psd_of_covariance`
factors `exp(−tψ(k_j−k_i))` into a rank-one positive matrix times the
entrywise exponential of `2t` times the anchored covariance kernel. This
proves PSD for every finite frequency sample and every `t≥0`.

Conversely, `heat_positive_negative` differentiates each zero-sum quadratic
form at `t=0` from the right. Positivity for every `t≥0` forces its derivative
`−energy(ψ,w)` to be nonnegative. Under the exact normalization `ψ(0)=0`
and evenness assumptions, `heat_positive_iff_negative` and
`heat_positive_iff_covariance` equate the full finite heat-multiplier PSD
property with conditional negativity and anchored covariance PSD.
`anisotropic_heat_positive_iff_active` then gives the exact mixed stable
criterion: if `a_j≥0` and `γ_j>0`, all finite matrices
`[exp(−t∑ a_r |k_{j,r}−k_{i,r}|^γ_r)]` are PSD at every nonnegative time
**iff** every positive-weight axis has exponent at most two. A zero-weight
superquadratic coordinate is harmless. Independent Lean checks cover the
quadratic endpoint, the zero-weight exception, and an active cubic failure.

This is the classical finite Schoenberg correspondence, with no novelty
claim. Literature anchor: I. J. Schoenberg, [*Metric Spaces and Positive
Definite Functions*, Transactions of the AMS 44 (1938), 522–536]
(https://www.ams.org/tran/1938-044-03/S0002-9947-1938-1501980-0/S0002-9947-1938-1501980-0.pdf).
The Lean proof uses the exact verified Stardust covariance/CND criterion,
Mathlib's Schur PSD theorem, the real exponential series and closed PSD
cone. These finite-matrix results do not yet construct a positive
convolution measure on the torus, identify a physical Markov semigroup,
establish a Lévy process, or imply a Bakry curvature/entropy inequality.
Original manuscripts remain byte-for-byte unchanged. Objective2 continues.

## Checkpoint1618: superquadratic heat multipliers fail finite positivity

`Foundation/FiniteBochnerObstruction.lean` connects the exact conditional-
negative threshold to the exponential heat multiplier. For any finite
three-point rate matrix `d` and zero-sum weights `w`, `expEnergy_deriv` proves
that the exponential quadratic form at time zero has derivative
`−energy(d,w)`. If that signed energy is positive, the form is negative at
some positive time (`expEnergy_eventually_negative`), so the sampled matrix
`[exp(−t d(i,j))]` is **not** positive semidefinite
(`non_psd_at_some_time`). The proof uses actual real differentiation and a
right-neighborhood limit, rather than asserting the full Schoenberg theorem.

`mixed_active_not_psd` applies this to every positive-weight coordinate with
exponent greater than two in the verified anisotropic stable symbol. The
offending coordinate can be embedded among arbitrary other coordinate
weights and exponents (the latter must be positive). Separately, the cubic
example gives an explicit time `t=log(10/9)>0`; its `(0,1,2)` sampled
multiplier has strictly negative quadratic form and fails PSD. Independent
Lean tests include cubic and quartic active axes.

This is a finite positive-definiteness obstruction to a characteristic or
convolution multiplier interpretation. The source does **not** prove a
physical-space positivity-preservation theorem for the completed Haar-L²
semigroup, construct a Lévy process, or establish an entropy/curvature
inequality. The positive direction (all exponentials PSD for a CND symbol)
would require a separately verified finite Schoenberg argument or explicit
process construction. The result is standard structure, with no novelty
claim. Original Bakry manuscripts and all ResearchSources bytes remain
unchanged. Objective2 continues.

## Checkpoint1617: exact active-axis criterion for mixed stable symbols

`Foundation/AnisotropicMixedThreshold.lean` closes the mixed converse left
open at1616. For a three-coordinate symbol
`ψ(k)=∑_j a_j |k_j|^γ_j`, assume every `a_j≥0` and `γ_j>0`. The verified
`anisotropic_negative_iff_active`, `anisotropic_covariance_iff_active`, and
`anisotropic_gamma1_iff_active` show that conditional negativity, anchored
covariance positivity, and nonnegative first algebraic Γ at the origin for
**every** finite Fourier polynomial are each equivalent to
`∀j, a_j>0 → γ_j≤2`. Under this condition,
`anisotropic_gamma_of_positive_axes` gives every finite Γ iteration,
pointwise, with zero imaginary part and nonnegative real part.

The converse restricts the symbol to frequency triples on any offending
coordinate axis. `mixed_on_axis` proves the restriction is precisely
`a_j|n|^γ_j`; the `(0,1,2)` triple with `(1,−2,1)` weights has exact signed
energy `2a_j(2^γ_j−4)>0` when `a_j>0` and `γ_j>2`. A zero-weight coordinate
does not contribute, even if its listed exponent is larger than two.
Independent Lean tests instantiate both patterns: weights `(1,0,2)` and
exponents `(2,4,1)` satisfy the criterion; weights `(1,1,0)` and exponents
`(1,3,4)` fail it, with explicit positive three-point energy.

These are finite Fourier, covariance and Γ statements; they do not establish
physical-space positivity preservation, a Lévy process, a diffusion
curvature bound, an entropy inequality, or a mass-gap conclusion. The proof
formalizes standard negative-type structure and makes no novelty claim. It
uses the retained original Bakry manuscript only as context; the manuscript
bytes remain unchanged. Full build, complete transitive axiom audit, all
public types/proofs, six independent tests and exact source/archive checks
are the milestone gate. Objective2 remains active.

## Checkpoint1616: sharp pure-axis exponent threshold and mixed quadratic endpoint

The existing `AnisotropicStableGamma` library established covariance and
algebraic Γ positivity for `0<γ_j<2`. `Foundation/AnisotropicStableEndpoint.lean`
extends the positive range to `0<γ_j≤2`, with nonnegative axis weights.
At `γ=2`, `axis_kernel_two` proves the actual kernel is the real Gram product
`k_j l_j`; `quadratic_kernel` gives the weighted dot product for an all-quadratic
symbol. The general mixed theorem uses this Euclidean endpoint together with
the verified fractional covariance result below two, finite PSD sums and the
existing covariance/CND equivalence. `anisotropic_gamma_le_two` supplies all
algebraic Γ iterations on every finite Fourier polynomial.

The converse is exact for each **pure coordinate** with `γ>0`.
`tripleWave=(0,1,2)` and zero-sum weights `(1,−2,1)` give conditional-negative
energy `2(2^γ−4)>0` whenever `γ>2`. Consequently
`axis_negative_iff_le_two`, `axis_covariance_iff_le_two` and
`axis_gamma1_positive_iff_le_two` prove, respectively, that CND, anchored
covariance positivity and all-polynomial Γ₁ positivity at the origin hold
**iff** `γ≤2` for positive γ. The converse is not claimed for an arbitrary
mixed symbol with a superquadratic coordinate and possibly zero weight; that
requires an explicit restriction-to-axis theorem and careful weight hypotheses.

These are classical Fourier/Schoenberg boundary facts formalized and connected
to the verified Gamma machinery, not a novelty claim or an actual Gaussian,
Lévy, or Brownian process construction. The primary Bakry manuscript at
`ResearchSources/bakry/bakry_emery_revised_v8 (2) (2).tex`, abstract and
Theorem A neighborhood (lines50–89, 205–251), states its stable results on
`0<γ<2`; its original bytes were preserved. The quadratic endpoint is an
explicit additional theorem, not silently inserted into the manuscript.

Verification1616: complete root build, complete transitive standard-axiom
audit, all 17 unabridged public types (15 proofs and two definitions), six
independent Lean tests, and exact source/config/archive hashes. Exact counts,
timings, commit and both PRIVATE remote receipts are in
`.lake/stardust-1616-verification.json`. Objective2 remains ACTIVE.

## Checkpoint1615: bounded multiplier rate with negative Γ₁

`Foundation/BoundedRateGammaObstruction.lean` chooses the two frequencies
`u=(1,1,1)` and `2u=(2,2,2)` and the rate
`r(k)=1` exactly at `k=±2u`, zero elsewhere. Lean proves `0≤r≤1`,
`r(-k)=r(k)` and `r(0)=0`. The explicit two-mode polynomial has coefficients
`1` at `u` and `−1/2` at `2u`. The verified finite Gamma calculation gives
`Re Γ₁(f,f)(0)=−1/4`. Consequently pointwise algebraic Gamma positivity,
the general conditional-negative-type criterion, and the anchored covariance
criterion all **fail** for this rate. The exact `not_negative_symbol` and
`not_covariance_symbol` declarations derive those conclusions through the
previously verified Fourier Gamma/covariance equivalences.

At the same time, `nnRate` is a valid nonnegative input to the completed
physical Haar-L² multiplier semigroup. `physical_contraction` proves the
actual L² contraction on the lifted witness; `physical_stationary_zero`
proves the constant Fourier mode stays fixed; `physical_witness_slope`
identifies the actual positive-time L² norm generator on the witness.
Thus L² contraction plus zero-mode conservation, even for a bounded even
rate, cannot be substituted for a positive Γ/covariance theorem.

This is an elementary finite counterexample, with no novelty claim. The
connection to classical Schoenberg theory is discussed in the earlier
literature audit; the Lean theorem here is non-CND, not a separately proved
absence of every possible stochastic path model or a pointwise failure of
positivity of the physical semigroup. Those stronger process/operator claims
need their own hypotheses and proof. The original Bakry manuscript's stable
symbol restrictions remain essential: this artificial bounded rate is not a
stable or Lévy symbol.

Verification1615: full root build, complete transitive standard-axiom audit,
unabridged public theorem/type and definition review, six independent Lean
tests, and exact source/config/archive hashes. Counts, timings, commit and
both PRIVATE backup receipts are in `.lake/stardust-1615-verification.json`.
Objective2 remains ACTIVE.

## Checkpoint1614: exact finite-core bridge between the two physical models

`Foundation/WaveTorusCoreBridge.lean` constructs an explicit finite Fourier
polynomial lift into the normalized unit-torus Haar L² Hilbert basis.
`repr_lift` and `lift_coeff` prove exact agreement of every Hilbert coordinate
and actual Haar Fourier coefficient with the original Laurent coefficient;
`lift_injective` proves no finite polynomial is lost. This uses Mathlib's
`UnitAddTorus.mFourierBasis_repr`, not a postulated unitary.

`generator_coeff` proves the finite algebra's coefficientwise generator
formula. `lift_anisotropic_generator` then proves that the **actual physical
L² positive-time norm slope** of each lifted polynomial converges to the
lifted finite generator for every nonnegative anisotropic stable rate.
`physical_inner_lift` evaluates the actual Haar integral of any two lifted
polynomials by a finite coefficient sum. Combining that with the earlier
verified period-2π box formulas yields exact `physical_box_generator_energy`,
`physical_gamma1_energy` (when the real symbol vanishes at zero), and
`physical_norm_box_parseval`. Thus the two different physical constructions
have the **same finite-core norm and integrated generator/Γ₁ energies** under
their respective normalizations.

This is a coefficient and energy bridge, not a theorem that the pointwise
functions are equal under a verified rescaling map. In particular it supplies
no Markov positivity, sample paths, maximal-domain pointwise Γ or entropy.
The L² model uses the local normalized Haar `MeasureSpace UnitAddCircle`
instance from pinned Mathlib. An independent test initially exposed that
Lean's unrelated default `AddCircle.measureSpace 1` produces a different
integral expression; downstream uses must select the Haar instance explicitly.

Verification1614: complete root build, complete transitive standard-axiom
audit, 10 unabridged public types, nine proof bodies, the lift definition and
three local measure instances, five independent Lean tests, and full
source/config/archive integrity. Exact counts, timings, commit and both
PRIVATE remote receipts are in `.lake/stardust-1614-verification.json`.
Objective2 remains ACTIVE.

## Checkpoint1613: actual Haar-L² realization on the unit three-torus

`Foundation/PhysicalTorusWaveSemigroup.lean` transports the verified
`WaveDiagonalSemigroup` through Mathlib's **actual multivariate Fourier Hilbert
basis** `UnitAddTorus.mFourierBasis`. The local primary source is
`Mathlib/Analysis/Fourier/AddCircleMulti.lean`, especially
`mFourierBasis` and `mFourierBasis_repr` (lines263–280 in the pinned Mathlib).
The latter identifies Hilbert coordinates with physical Haar Fourier
coefficients; no formal or assumed coefficient-to-function map is inserted.

For every nonnegative frequency rate `r : (Fin 3 → ℤ) → ℝ≥0`, the transported
operators on `Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin 3)))` are contractions,
obey the semigroup law, and are strongly continuous in nonnegative time.
`evolution_coeff` gives the exact physical Fourier multiplier;
`evolution_mode` and `stationary_mode` test its action on actual L² Fourier
modes. `generator_iff` proves that the positive-time L² norm slope converges
to `g` **iff** every actual Haar Fourier coefficient of `g` is
`-r(k)` times that of `f`. `generator_domain` gives the exact weighted ℓ²
maximal domain, and `graph_closed` proves the physical generator graph closed.
`anisotropic_generator_iff` and `anisotropic_generator_domain` specialize this
to the existing nonnegative anisotropic stable symbol. These are completed
physical-space operator results, stronger than the earlier finite Fourier
core and abstract coefficient-space statements.

The unit torus here has period **one**; the preceding real-coordinate
`boxAverage`/`synthesis` core uses period **2π**. Their normalization/scaling
identification is not yet a verified theorem, so the two physical models are
not silently equated. Positivity preservation, Markov kernels, a Lévy process,
pointwise or maximal-domain Γ/CD identities, invariant entropy and LSI also
remain open. A complex L² contraction alone establishes none of these.

Verification1613: full root build 6863 jobs; complete standard-three-axiom
transitive audit 51885 safe Foundation declarations; 19 unabridged public
types, 14 public theorem proofs, five public definitions/abbreviations, one
private coercion lemma and three local instances reviewed; five independent
Lean examples; source/config/archive integrity checked. Exact Git and private
backup evidence is recorded in `.lake/stardust-1613-verification.json` and the
guarded synchronization receipts. Objective2 remains ACTIVE.

ACTIVE since user-authorized transition6615f16; Objective1 remains deferred and
incomplete. This audit is a partial deliverable, not completion of Objective2.

## Initial reuse and literature audit (October27, checkpoint1602)

The brief displays (psi(xi)+psi(eta)-psi(xi+eta))/2. On a complex Fourier core
this is a bilinear convention; the existing conjugate-linear first slot uses
psi(eta-xi), as defined in FiniteStableGamma.Core.kernel and proved for the
actual recursive Gamma by gammaIter_single. For psi(x)=x^2 the displayed plus
kernel at(1,1) is -1, so it cannot be treated as a positive covariance kernel.
For even psi it is the difference-kernel evaluated at(-xi,eta), a cross pairing,
not the Gram matrix obtained by changing both arguments together.

The difference-kernel/conditional-negative-type correspondence is established
mathematics. Hermine Bierme, Introduction to random fields and scale invariance,
LectureI (April4,2016), PDF pages18–20 (zero-indexed), states the stationary-
increment covariance and Schoenberg equivalence. Ramesh Gangolli, Annales IHP B
3(2),1967,121–226, ChapterI, introduces Levy–Schoenberg kernels and describes
the corresponding conditionally negative functions and Gaussian covariances.
Only these relevant sections were examined, not the whole107-page paper.
Sources:
- https://www.lebesgue.fr/sites/default/files/attach/Bierme_Lecture1.pdf
- https://www.numdam.org/item/AIHPB_1967__3_2_121_0.pdf
No novelty is claimed for the finite anchored-kernel theorem below. Full
Levy–Khintchine, Bernstein subordination, exponential-positive-definite and
infinite process realizations have NOT been verified by this checkpoint.

Exact reusable declarations:
- FiniteStableGamma.Core.kernel, gammaIter_single, gammaIter_finite: actual
  signed Fourier multiplier/Gamma algebra, requiring no probabilistic positivity.
- FiniteStableGamma.Core.stable_kernel_covariance and
  FractionalCovarianceMatrices.covarianceMatrix_posSemidef: genuine fractional
  covariance for0<H<1, with sign and parameter hypotheses explicit.
- FractionalCovarianceMatrices.hurst_two_negative_energy: preserved quartic
  covariance obstruction; the new zero-sum test agrees with it.
- FractionalFourierSemigroup.contraction,strong_continuity,generator_iff:
  nonnegative rates give a genuine L2 contraction semigroup and exact domain.
  This alone does not give Markov positivity or covariance positivity.
- FractionalCovarianceMatrices.covariancePower_posSemidef and Mathlib's
  Matrix.PosSemidef.hadamard: existing route to integer kernel powers, not a
  positive curvature constant or comparison between successive powers.

## Finite general theorem and exact limitations

Foundation.AnchoredCovariance defines finite real energy c^T d c and the
anchored kernel K_o(i,j)=(d(i,o)+d(o,j)-d(i,j))/2. Center c by subtracting its
total mass at the anchor o. `covariance_identity` proves
2*c^T K_o c = -(centered c)^T d (centered c), assuming only d(o,o)=0.
`anchored_positive_iff` gives the exact quadratic-form equivalence;
`anchored_posSemidef_iff` adds symmetry and proves the genuine matrix PSD
iff conditional negativity on ALL zero-sum coefficient vectors.
No positive-definiteness assumption is smuggled into the hypothesis.

`fourier_covariance_iff` directly uses the verified FiniteStableGamma kernel:
for any even real symbol psi with psi(0)=0 and finite frequency family including
a specified zero-frequency anchor, its Hermitian Gamma kernel is PSD iff the
sampled distance matrix psi(k_j-k_i) is conditionally negative. The anchor
membership requirement is explicit; arbitrary unanchored samples have not yet
been handled by adjoining zero in this module. This is a finite algebraic
criterion, not construction of a Levy process or proof of a curvature bound.

Independent exact tests include the quartic distance on{0,1,2} with zero-sum
weights(-1,2,-1): its energy is24>0, so conditional negativity fails. In contrast,
the existing1601 spectral semigroup allows fourth-power rates. Thus spectral
contractivity does not discharge this covariance criterion. The plus-sign
quadratic kernel fails even its one-point diagonal test. Neither obstruction
invalidates the signed pseudoprocess algebra or the verified stable regime.

Next: extend the finite criterion to arbitrary sampled sets by adjoining the
anchor, and assess which symbol constructions discharge conditional negativity
using existing Hilbert/increment representations. Then examine whether the
result adds any curvature comparison beyond Schur positivity. Preserve all six
Objective2 deliverables; literature novelty and full process/domain obligations
remain open. Do not reopen IBM or switch campaigns.

## Verification1602

Full6852-job root build43.254s; complete51695-declaration safe transitive audit
44.079s (only propext, Classical.choice, Quot.sound). All14 public types,
10 full proofs and4 definitions reviewed unabridged; no new local instances or
options. Four independent Lean checks passed29.349s. The first independent run
failed only finite-function/conjugate-transpose/square-normalization elaboration;
repaired without production changes. Scratch1–6 finite-sum factoring and matrix
coercion errors were repaired explicitly; scratch7 passed. Failed logs retained,
not mathematical counterexamples. Warnings remain visible; no settings change.
Source2673/config3/archive113 integrity matches frozen manifests; original
manuscripts are unchanged. Exact local commit/receipt follow. REMOTE SYNC QUEUED
under the weekday09–17 Eastern policy; no backup claimed until verified.
Objective2 remains ACTIVE and incomplete; Objective1 deferred/incomplete.

## Checkpoint1603 — arbitrary samples and Hilbert increments (October27)

FourierCovarianceCriterion removes1602's requirement that a sampled family
already contain frequency0. `withZero` adjoins0 using Option; `negative_restrict`
extends coefficients by0 and restricts conditional negativity. Principal
submatrix positivity transfers the anchored covariance back to the original
sample. Empty samples, repeated frequencies and signed frequencies are allowed.
`symbol_iff` states the exact equivalence on ALL finite samples for even symbols
vanishing at0, on the existing Wave=(Fin3->Z) frequency group. It is not yet a
continuum R^d symbol theorem, an exponential-positive-definite theorem or a
Levy-process construction. No sampled positivity is postulated in the forward
conditional-negative direction.

`hilbert_kernel` identifies the actual Fourier Gamma kernel with inner(vk,vl)
when psi(k)=||vk||^2 and psi(l-k)=||vl-vk||^2. `hilbert_covariance` uses the
actual Gram-matrix positivity theorem, and `hilbert_negative` derives psi0=0,
evenness and conditional negativity from those exact representation hypotheses.
This is a sufficient representation theorem; it does not construct v for an
arbitrary symbol or infer a Markov generator from an arbitrary covariance.

`stable_covariance` and `stable_negative` discharge the global criterion for
0<gamma<2 by DIRECT reuse of FractionalCovarianceMatrices and the verified
stable_kernel_covariance identity, without assuming a new process or frequency
sign restriction. The current stableSymbol depends on coordinate0, so this is
a potentially degenerate rank-one symbol on Wave, not an asserted isotropic
three-dimensional symbol. Independent tests also realize the quadratic symbol
through H=R and v(k)=k0, outside the open fractional parameter range. These are
known covariance principles under the literature audit1602; no novelty claimed.

Independent exact tests cover quadratic Hilbert realization, failure of
NegativeSymbol for fourth-power rates using the three-point zero-sum vector,
an empty covariance sample, and arbitrary two-frequency Cauchy samples.
Thus the global quantifiers do not hide an anchor/nonempty/distinctness
requirement, and the higher-order signed obstruction remains preserved.

NEXT connect this general criterion to the ACTUAL iterated Fourier Gamma
recursion using existing gammaIter_finite, complex phase-energy identities and
Hadamard powers. Determine the exact finite-core positivity/curvature statement
it yields, rather than inferring a positive curvature constant, spectral gap,
completed domain or jump LSI from covariance alone. Preserve all six Objective2
deliverables; Objective1 remains deferred/incomplete.

Verification: final full6853-job build44.183s; complete51706-declaration safe
transitive audit45.163s (only propext, Classical.choice, Quot.sound). All11
unabridged public types,8 full proofs and3 definitions reviewed; no new local
instances/options. Four independent checks passed first run27.060s. Initial
scratch failed Option.elim argument order; second passed. Initial full build
passed42.877s; source review caught a leading-space definition omitted by the
public-name extraction helper. It was added to explicit type/axiom lists,
formatting normalized and source manifest refreshed; final full build and
complete audit rerun. No theorem or requirement weakened; logs retained.
Source2674/config3/archive113 hashes exact. ResearchSources unchanged. Exact
commit/receipt follow; REMOTE SYNC QUEUED under weekday09–17 Eastern policy.
Objective2 ACTIVE/incomplete; Objective1 deferred/incomplete; laterqueue intact.

## Checkpoint1604 — actual finite-core iterated Gamma positivity (October27,2026)

Objective2 ACTIVE. Foundation/FourierGammaCovariance.lean connects the general
covariance criterion to the existing ACTUAL generator recursion, rather than
only asserting positivity of an auxiliary matrix. `gamma_energy` identifies
the synthesized nth Gamma iteration with the complex energy of the entrywise
nth power of Kpsi, with phases c_i character(k_i,x). `power_psd` uses the Schur
product theorem (including n=0/all-ones); `energy_nonnegative` reuses the existing
real/imaginary energy identities. `gamma_finite_nonnegative` handles arbitrary
finite presentations, and `gamma_nonnegative` passes through the exact support
representation to EVERY f in the existing finite Fourier algebra, all n:N and
all spatial points. `negative_symbol_gamma` applies the1603 equivalence for
even, zero-normalized conditionally negative symbols. No frequency-sign or
distinctness restriction is introduced; conjugation remains in the first slot.

Thus Gamma2>=0 is established pointwise on this finite core for such symbols.
This is a known Schur/covariance consequence, not a novelty claim or a positive
curvature constant. No completed pointwise domain, Markov semigroup, stochastic
process, LSI or spectral gap is inferred. The symbol group remains Z^3, and the
existing stable example remains coordinate0/rank-one. Objective1's different
completed-domain, drift and entropy obligations remain deferred/incomplete.
Literature context remains the exact classical covariance sources in1602;
further family/subordination and novelty audits remain required.

Four independent checks passed: quadratic Hilbert symbol for all n/f/x;
Cauchy Gamma2 for arbitrary f/x; Gamma0 positivity for arbitrary symbol;
quartic CovarianceSymbol failure via the explicit three-point zero-sum test.
The last prevents applying the theorem indiscriminately to pseudoprocess rates.
NEXT investigate the converse finite-core Gamma1 criterion and its explicit
quartic pointwise witness, then productive general Levy/subordination examples.
Retain all six Objective2 deliverables and the later queue.

Verification: full6854-job build45.8204555s; complete51712-declaration safe
transitive axiom audit46.0396493s, whitelist propext/Classical.choice/Quot.sound.
All six unabridged public types and six full proofs reviewed; no new definitions,
local instances or options. Four independent proofs passed first run27.2934204s.
Initial scratch elaboration failures involved matrix coercion/Hadamard unfolding
and a missing namespace; repaired without changing hypotheses or options, with
all logs retained. Final scratch passed before adoption. Source2675/config3/
archive113 hashes exact; ResearchSources unchanged. Exact Git commit/receipt
follow. REMOTE SYNC QUEUED under the weekday09–17 Eastern policy, not backed up.

## Checkpoint1605 — exact finite-core Gamma1 criterion and explicit quartic failure (October27,2026)

Objective2 ACTIVE. `Foundation/FourierGammaCriterion.lean` proves a converse to
checkpoint1604. For an EVEN real symbol psi on the existing Wave=Z^3, positivity
of the REAL part of actual synthesized Gamma1(f,f) at the single spatial origin
for EVERY finite Fourier polynomial f is EQUIVALENT to global positive
semidefiniteness of all finite matrices Kpsi(k_i,k_j). The converse uses real
Fourier coefficients and the exact `real_gamma_energy` identity; evenness
supplies the Hermitian matrix condition. With psi(0)=0, the1603 symbol theorem
makes this equivalent to conditional negativity of psi on ALL finite samples.
No pointwise positivity at all spatial points is assumed in the converse; the
forward result1604 does give it. Finite presentations may repeat frequencies.

`quarticWitness` has frequencies 0,1,2 in the existing coordinate0 symbol and
coefficients -1,2,-1. The ACTUAL Gamma1 synthesis for stableSymbol 4 at the
origin has real value EXACTLY -12. This sharpens the prior negative-energy
matrix obstruction to a concrete failure inside the Fourier operator calculus.
The independent scratch also calculates a cubic-rate example: frequencies1,2,
coefficients4,-1 yield Gamma1 value -8. These higher-order rates cannot meet
the covariance/pointwise Gamma positivity criterion. Signed pseudoprocess
operator identities still exist; no Markov or process conclusion follows.

The equivalence is the classical negative-type/positive-kernel principle made
exact for the existing verified Fourier operator core. The sources in checkpoint
1602 (Bierme2016 LectureI and Gangolli1967 ChapterI) remain the novelty baseline;
no new stochastic curvature, positive kappa, CD bound, spectral gap, completed
pointwise domain or sharp entropy estimate is claimed. Objective1's unfinished
manuscript, drift, domain and entropy work remains deferred/incomplete.

Five independent Lean checks passed: the iff at exact hypotheses, explicit
quartic negativity, all-iteration quadratic Hilbert example, quartic failure
of the negative-symbol property via the actual witness, and a separately
calculated cubic witness. Original manuscript hashes preserved. NEXT examine
whether the evenness assumption can itself be derived from Gamma1 positivity
when psi(0)=0; then test actual Levy/subordination symbols and the limits of
passing from finite-core Gamma inequalities to closed Markov domains. Preserve
all six Objective2 deliverables and the authoritative later queue.

Verification: final full6855-job root build42.1936043s; complete51726-declaration
safe transitive axiom audit44.4928919s with only propext/Classical.choice/
Quot.sound; all ten unabridged public types, seven full theorem proofs, three
definitions, and five independent proofs reviewed. No new local instances,
options, sorry/admit or axiom. Final source2676/config3/archive113 hashes exact.
The first full build passed but two new-file style warnings were repaired;
the full build was rerun on the final bytes. Scratch elaboration repairs used
the explicit matrix type and separated real-energy rewrite; no hypotheses
changed. Exact Git commit/receipt follow. REMOTE SYNC QUEUED under weekday
09–17 Eastern policy, never reported as remotely backed up.

## Checkpoint1606 — normalization, symmetry and the weak negative-symbol obstruction (October27,2026)

Objective2 ACTIVE. `Foundation/FourierGammaNormalization.lean` proves that the
evenness hypothesis in1605 is AUTOMATIC from universal actual Gamma1 positivity
at the spatial origin when psi(0)=0. The exact two-frequency formula for the
polynomial supported on {0,k}, with real coefficients (t,1), is
Gamma1=psi(k)+t(psi(k)-psi(-k))/2. If the odd part is nonzero, a concrete t
makes this -1. Thus `normalized_gamma_iff_covariance` gives an exact equivalence
between universal finite-core origin Gamma1 real positivity and ALL finite
Kpsi matrices positive semidefinite, with no assumed symmetry. Together with
1603, `normalized_gamma_iff_negative_even` gives the precise alternative:
conditional negativity AND evenness. Theorem statements quantify all finite
Fourier polynomials on the existing Wave=Z^3; there is no frequency-sign,
distinctness, probability-process or completed-domain assumption.

Crucial qualification: the repository predicate `NegativeSymbol` currently
contains ONLY the zero-sum quadratic inequality. Its definition does not impose
the symmetry/Hermitian clause of standard negative-type conventions. The new
`antisymmetric_energy_zero` and `odd_symbol_negative` prove EVERY odd real
symbol passes that inequality: antisymmetric distance matrices contribute
zero to all real quadratic forms. The concrete `linearSymbol(k)=k0` satisfies
`NegativeSymbol` but the actual Gamma1 of `pairPolynomial(1,-2)` at the origin
has value -1. An independent cubic odd symbol gives the same discrepancy.
Hence neither the weak predicate nor its odd examples certify a symmetric
Levy exponent, positive covariance kernel, Markov generator or curvature.
The evenness clause must be kept in `symbol_iff` and any stochastic reading.
This is a precise correction of the hypothesis bookkeeping, not a claim of
novelty in classical negative-type theory.

Five independent checks passed: odd cubic weak conditional negativity; its
directly calculated Gamma1 value -1; symmetry consequence under exact h0 and
Gamma positivity; positive normalized Cauchy/stable example; and direct
negative linear witness. No original manuscript was changed. NEXT investigate
the necessity of normalization and test whether an unnormalized odd symbol can
have nonnegative real Gamma1 through a positive constant component; then pursue
actual Levy/subordination examples and domain/curvature limits. Objective1
remains deferred/incomplete, and all six Objective2 deliverables stay open.

Verification: final full6856-job build41.5229945s; complete51744-declaration
transitive axiom audit44.2039499s, whitelist only propext/Classical.choice/
Quot.sound; all13 unabridged public types,9 full proofs,4 definitions and5
independent proofs reviewed. No local instances/options/sorry/admit/axioms.
Final source2677/config3/archive113 hashes exact. The first full build passed;
a duplicate new-file header was removed and the full build rerun on final bytes.
Scratch simplification/algebra fixes and source log evidence retained.
ResearchSources unchanged. Exact commit/receipt follow. REMOTE SYNC QUEUED
under weekday09–17 Eastern policy, never claimed remotely backed up.

## Checkpoint1607 — why origin normalization matters for real Gamma positivity (October27,2026)

Objective2 ACTIVE. `Foundation/FourierGammaAsymmetry.lean` constructs the exact
unnormalized symbol psi(k)=2+(k0)^2+k0 on Wave=Z^3. Its actual Fourier Gamma1
kernel is Kpsi(k,l)=1+k0*l0+k0. For ANY finite real coefficient family c,
the associated quadratic energy is S^2+T^2+S*T, where S=sum c_i and
T=sum c_i*k_i0; completing the square proves it nonnegative. The existing
complex energy decomposition extends this to arbitrary complex coefficients
and Fourier phases. Consequently the REAL part of synthesized Gamma1(f,f)
is nonnegative for EVERY finite Fourier polynomial f at EVERY spatial x.

However psi(0)=2 and psi is not even. With `imaginaryWitness` (coefficients
1 at zero and i at frequency1), actual synthesized Gamma1 at the origin has
imaginary part EXACTLY -1. The verified `offset_not_covariance` concludes the
finite Kpsi matrices cannot all be positive semidefinite; the summary theorem
packages universal real Gamma1 positivity with this failure. Thus replacing
the normalized criterion1606 by REAL-part positivity without psi(0)=0 is
mathematically false. The independent check centers the same symbol by
subtracting2 and computes real Gamma1=-1 using the two-frequency polynomial.
The constant offset masks the odd part in the real energy, while the complex
imaginary part still detects non-Hermitian behavior. This is a finite-core
operator counterexample, NOT a stochastic process or a Levy exponent.

Independent Lean checks cover psi0=2, explicit non-evenness, arbitrary-point
real positivity, nonzero imaginary Gamma1, and the centered negative witness.
No original manuscript changed. Classical finite-matrix algebra; no novelty
claim against Schoenberg/Levy-Khintchine literature. NEXT investigate whether
reality AND nonnegativity of Gamma1 for all COMPLEX finite Fourier polynomials
give an exact unnormalized PSD criterion by polarization; test minimal probes.
Then resume actual symmetric Levy/subordination examples and distinguish
finite-core Gamma2 from completed Markov curvature/domains. All six Objective2
deliverables and later campaigns remain; Objective1 deferred/incomplete.

Verification: full6857-job root build43.0623554s; complete51758-declaration
transitive axiom audit43.2776311s allowing only propext/Classical.choice/
Quot.sound; all10 unabridged public types,8 full proofs,2 definitions and5
independent proofs reviewed. No new instances/options/sorry/admit/axioms.
Source2678/config3/archive113 hashes exact, ResearchSources unchanged.
Initial scratch elaboration fixed finite-sum factoring, explicit subtype
coefficients and the two-frequency complex energy; final scratch passed before
adoption. Exact Git commit/receipt follow. REMOTE SYNC QUEUED under weekday
09–17 Eastern policy; do not claim remotely backed up before verification.

## Checkpoint1608 — complete complex Gamma1 covariance criterion without normalization (October27,2026)

Objective2 ACTIVE. `Foundation/FourierGammaComplexCriterion.lean` proves an exact
finite-core operator criterion for EVERY real symbol psi on the existing
Wave=Z^3, WITHOUT psi(0)=0 or an assumed symmetry clause: ALL finite matrices
Kpsi(k_i,k_j) are positive semidefinite if and only if actual synthesized
Gamma1(f,f) at the spatial origin is REAL and has NONNEGATIVE real part for
EVERY finite Fourier polynomial f. This is `gamma_full_iff_covariance`.

The reality requirement can be reduced to the two-frequency probes
`imaginaryPair(k,l)=single(k,1)+single(l,i)`. Their Gamma1 imaginary part is
EXACTLY Kpsi(k,l)-Kpsi(l,k), so their reality forces all kernels symmetric
and even forces psi(-k)=psi(k), with no zero-normalization needed. Positive
real Γ1 on arbitrary finite inputs then yields the real matrix quadratic
inequality. `gamma_complex_iff_covariance` states this smaller reality-test
family explicitly. The converse reuses checkpoint1604's all-iteration
Gamma positivity and reality from genuine finite covariance matrices.
Repeated frequencies and all finite sample types are included. This is
classical Hermitian polarization, not a novel stochastic curvature theorem.

The offset example1607 proves the imaginary clause is essential: real Γ1 is
nonnegative at every point, but a 1,i probe has imaginary value -1. The
normalized result1606 proves a distinct route to symmetry when psi0=0 and
real positivity is universal. Neither theorem constructs a Markov process,
closed generator, positive curvature constant, spectral gap or LSI. Standard
negative-type and Levy–Khintchine assumptions must still be checked before
interpreting any symbol as a stochastic generator. The exact literature
baseline remains Bierme2016 LectureI and Gangolli1967 ChapterI from1602;
no novelty is claimed for polarization or Schoenberg theory.

Four independent Lean checks passed: the linear odd symbol's explicit 1,i
imaginary value -1; offsetSymbol fails the full criterion; the verified
Cauchy/stable symbol passes it for arbitrary Fourier f; and two-point
reality yields evenness for an arbitrary symbol. NEXT leave this finite
matrix audit for a productive symmetric Levy/subordination example (possibly
anisotropic coordinatewise stable symbols) and test which exact operator
or semigroup hypotheses follow. All six Objective2 deliverables and later
queue obligations remain; Objective1 deferred/incomplete.

Verification: full6858-job root build44.5048240s; complete51765-declaration
transitive axiom audit45.9444821s, whitelist only propext/Classical.choice/
Quot.sound; all7 unabridged public types,6 full proofs,1 definition and4
independent proofs reviewed. No local instances/options/sorry/admit/axioms.
Source2679/config3/archive113 hashes exact; ResearchSources unchanged.
Initial scratch polynomial identity needed a final ring step; final scratch
passed before adoption. Exact Git commit/receipt follow. REMOTE SYNC QUEUED
under weekday09–17 Eastern policy, not yet remotely verified.

## Checkpoint1609 — anisotropic stable covariance and curvature-scale obstruction (October27,2026)

Objective2 ACTIVE. `Foundation/AnisotropicStableGamma.lean` proves finite
covariance-symbol matrices form a cone under zero, addition, nonnegative
scaling and finite sums. For each coordinate of Wave=Z³, its symbol
`|k_j|^γ` has the verified fractional covariance kernel when `0<γ<2`.
Consequently `anisotropicSymbol a γ = ∑_j a_j |k_j|^(γ_j)` has finite
covariance PSD and weak conditional negativity for every `a_j≥0` and
`0<γ_j<2`. It has zero origin and even symmetry. The actual finite Fourier
Γ_n synthesis is real and nonnegative for every order, finite polynomial
and spatial point. This is a theorem about finite Fourier polynomials and
matrices, not a Lévy-process construction or completed generator domain.

The independent test uses weights `(1,2,0)` and exponents `(1,3/2,1/2)`:
its nonzero third-axis frequency has symbol exactly zero. Thus the general
nonnegative-weight theorem supplies no strictly positive lattice rate or
spectral gap. Separately `halfCauchy=(1/2)*stableSymbol 1` still has covariance
PSD, but the actual single-mode Γ_n value is `(1/2)^n`; in particular
Γ₂=1/4<Γ₁=1/2. A scale-free Γ₂≥Γ₁ implication from covariance is false.
This does not contradict the *unit-scale* Cauchy theorem proposed in
`ResearchSources/bakry/hurst_curvature.tex`; it rules out extending its
constant unchanged to arbitrary rate rescalings. That manuscript, title
*Curvature on the Hurst Line: Graded Bakry–Émery Curvature, Wiener Chaos, and
Iterated Brownian Motion*, SHA256
`0762018E4F05FC1A91E9065983FB0C650E389E51CDFFD5818268E4F33B53D8FA`
(71,893 bytes), was reviewed selectively at abstract lines58–118 and
theorem lines170–210. Its all-order and A(4) claims remain unverified here;
the manuscript is preserved byte-for-byte. The fractional covariance and
negative-type facts are classical; no novelty is asserted.

Five independent Lean examples checked a nontrivial mixed symbol's PSD,
all-order Γ positivity, zero-frequency degeneracy, half-scale Γ₁/Γ₂ values
and negative-type conclusion. Full6859-job root build42.3449486s;
complete51788-declaration transitive axiom audit45.3896695s, whitelist
only propext/Classical.choice/Quot.sound; all19 unabridged public types,
14 full proofs,5 definitions and5 independent proofs reviewed. No local
instances/options/sorry/admit/axioms. Source2680/config3/archive113 hashes
exact; ResearchSources unchanged. Exact Git commit/receipt follow; remote
sync QUEUED by weekday09–17 Eastern restriction, not remotely verified.
NEXT test whether the anisotropic symbol supports a genuine L² contraction
semigroup and exact graph domain using existing Fourier machinery; retain
the distinction from positivity-preserving Markov semigroups and any
physical stochastic realization. Objective2's six deliverables remain open.

## Checkpoint1610 — closed anisotropic diagonal semigroup on ℓ²(Z³) (October27,2026)

Objective2 ACTIVE. `Foundation/WaveDiagonalSemigroup.lean` constructs, for
every nonnegative rate `r : Wave → ℝ≥0`, an actual bounded diagonal evolution
on the Hilbert coefficient space `lp (fun _ : Wave => ℂ) 2`. It proves
contraction, time-zero identity, semigroup composition and strong continuity.
Its right difference quotient converges in the full Hilbert norm EXACTLY when
`(f,g)` belongs to the multiplier graph `g(k)=-r(k)f(k)`. This graph is closed,
and its domain is precisely weighted ℓ² membership. The anisotropic rate from
1609 satisfies the required nonnegativity, and its generator and domain are
identified without imposing artificial finite-support restrictions. A mode
at any zero-rate frequency is nonzero and stationary. The independent mixed
example has precisely such a third-axis frequency, confirming that general
nonnegative weights do not imply strict contraction or a positive spectral
gap. The proof reuses the 1D fractional semigroup's real quotient bound and
limit; the three-coordinate Hilbert convergence is proved explicitly.

This is a genuine strongly continuous *operator* semigroup on Fourier
coefficients. Identification with normalized Haar L² on the physical 3-torus,
positivity preservation, conservativity as a Markov semigroup, a Lévy-process
realization, and extension of pointwise Γ_n to the graph domain remain OPEN.
Covariance PSD from1609 alone does not discharge any of those obligations.
The distinction is required before any CD, entropy or LSI application. The
result is a direct diagonal-multiplier construction; no novelty is claimed
against standard semigroup theory.

Verification: full6860-job root build11.2976163s after the source was already
compiled in an initial41.4602003s build; complete51827-declaration
transitive axiom audit43.6098201s, allowing only propext/Classical.choice/
Quot.sound; all29 unabridged public types,21 full proofs,8 definitions/
abbreviations and5 independent Lean proofs reviewed. No local instances,
options, sorry, admit or axioms. Source2681/config3/archive113 hashes exact;
ResearchSources unchanged. Exact commit/receipt follow. Remote sync QUEUED
under the weekday09–17 Eastern rule.

Audit-evidence incident: the first cloned stage runner retained checkpoint1609
output paths. It ran a successful6860-job build and the OLD1609 audit file,
overwriting the local `.lake/stardust-1609-{full-build,audit}.log` and timing
files. The original1609 exact receipt and terminal verification JSON retain
their original SHA256 values and prior successful counts, but the two raw log
files no longer match those hashes. The runner was corrected before any1610
approval; fresh independent1610 full-build, complete audit and check files
are kept under distinct1610 paths. No mathematical source or committed record
was modified by this error. Do not represent the replaced1609 raw logs as
recoverable original evidence. A later verified descendant can back up both
committed results; no claim of remote verification is made here.

NEXT link the coefficient semigroup to physical torus Haar L² and test
Markov positivity independently, or exhibit a precise failure. Objective2's
remaining deliverables and later campaign order are unchanged.

## Checkpoint1612 — physical finite-torus Parseval and integrated Γ₁ energy (October27,2026)

Objective2 ACTIVE. `Foundation/WavePhysicalFourierBridge.lean` links the
three-coordinate finite Fourier calculus to the ACTUAL normalized iterated
box integral from `FiniteFourierTorusAverage`. For any finite distinct
frequency family, `box_inner` proves exact physical orthogonality and
`box_parseval` proves its norm identity. The canonical support presentation
`polynomial_support` removes that distinct-list hypothesis for arbitrary
finite Fourier polynomials: `box_parseval_all` identifies the physical
integral of `conj(synthesis f)*synthesis f` with the finite sum of coefficient
moduli squared. This is a genuine integral, not a formal constant trace.

For EVERY real symbol `a` and finite polynomial, `box_generator_energy_all`
computes negative physical generator pairing exactly as
`∑_{k∈support f} a(k) conj(f_k) f_k`. Nonnegative rates yield physical
finite-core dissipativity. Under `a(0)=0`, the actual integrated first Gamma
equals that generator energy (`box_gamma1_energy`). The anisotropic symbol from1609
discharges normalization and nonnegative rate, so the physical Γ₁/energy
identity and nonnegative real energy hold for every finite polynomial.
Combining the 1609 covariance theorem additionally gives pointwise finite
Γ_n positivity when `a_j≥0` and `0<γ_j<2`; the physical identity itself
does not require the upper exponent bound or covariance PSD.

The zero-normalization is mathematically material: the independent test
uses constant symbol `a≡1` and the constant Fourier mode. Its integrated
Γ₁ value is EXACTLY1/2, whereas its negative generator energy is EXACTLY1.
Thus the unnormalized equality is false. No claim that `a(0)=0` is logically
necessary for every possible symbol is made; this explicit counterexample
shows the hypothesis cannot simply be omitted. Distinctness is required in
the indexed finite-family formula because repeated frequencies combine
coefficients; the canonical support theorem handles repetitions correctly.

This bridge does NOT construct the completed physical Haar-L² torus,
identify checkpoint1610's ℓ² semigroup with a physical-space operator,
prove positivity preservation or a Markov/Lévy process, extend Γ to the
maximal graph, or establish CD, entropy or LSI. Parseval and integrated
Dirichlet identities are standard Fourier mathematics; no novelty claim.
The exact cross-library reuse is `FiniteFourierTorusAverage.boxAverage_synthesis`,
`FiniteStableGamma.Core.gammaIter_finite`, `FiniteFourierReality.synthesis_reflection`,
and the 1609/1610 anisotropic symbols/rates.

Five independent Lean checks covered arbitrary-polynomial Parseval, the
normalized integrated identity for an odd real symbol (no symmetry premise),
mixed anisotropic physical dissipativity, and both sides of the constant-
symbol counterexample. Full6861-job root build44.7466709s; complete51843-
declaration transitive axiom audit47.2580528s with only propext,
Classical.choice and Quot.sound; all13 unabridged public types,12 full
proofs,1 definition and5 independent proofs reviewed. Source2682/config3/
archive113 hashes exact, ResearchSources unchanged, no local instances,
options, sorry, admit or axioms. Exact commit/receipt and immediate guarded
PRIVATE backup follow under the lifted intraday restriction.

NEXT establish a rigorous physical Haar-L² Fourier identification and
intertwining for the closed ℓ²(Z³) semigroup, then test Markov positivity
and graph-domain Γ under exact hypotheses. Objective2 remains incomplete.

## Checkpoint1623 — real Markov order and actual probability approximants (October27,2026)

`Foundation/PhysicalHeatMarkovOrder.lean` extends the physical Haar-L² cone
theorem. For every covariance symbol and every real input, the multiplier
evolution remains real; for ordered real inputs it remains ordered. If the
constant frequency has rate zero, every almost-everywhere real interval
`[m,M]` is preserved, including the essential absolute bound. The interval
statement is a genuine completed-L² maximum principle; it does not require
pointwise representatives or boundedness for the general monotonicity theorem.

For each finite Fourier `f` with squared coefficient energy one, the evolved
square has a continuous nonnegative density of Haar integral one. Thus
`heatSquareProbability` is an actual probability measure on the compact
three-torus. Its exact character expectation is
`exp(-t r(k)) * (reflection f * f).coeff k`, proved with the real density
integral rather than inferred from a formal trace. These probability measures
depend on `f`: no exact transition kernel, compatible convolution laws,
finite-dimensional process, or path-space law is asserted. The decisive next
step is a normalized finite Fourier approximate identity whose squared
Fourier coefficients converge to one at every fixed frequency, followed by
a compact probability-measure limit and exact character/semigroup tests.
Schoenberg/Herglotz measure existence is classical; its torus realization is
not yet a theorem in this module. The Riesz–Markov–Kakutani positive-functional
API in Mathlib offers another route, but positivity and uniform extension of
the finite Fourier functional would need explicit proof.

This is directly relevant to Objective2: verified covariance positivity now
has a conservative order-preserving physical L² evolution and genuine
probability approximants. No curvature bound, entropy inequality, stochastic
process, or IBM/black-noise conclusion follows. Full6873-job root build and
complete52117-declaration transitive axiom audit passed with only propext,
Classical.choice and Quot.sound. All18 unabridged public types,16 full proofs,
2 definitions,3 local instances and5 independent tests were reviewed.
Source2693/config3/archive113 hashes matched; ResearchSources is unchanged.
Exact commit, receipt and PRIVATE dual-ref verification follow.

## Checkpoint1624 — conditional compactness limit for a transition law (October27,2026)

`Foundation/PhysicalHeatTransitionLimit.lean` proves an exact measure-level
reduction. Given a sequence of unit-energy finite Fourier polynomials whose
square autocorrelation coefficient tends to one at every fixed wave number,
the genuine heat-square probability measures from1623 have a weakly
convergent subsequence. Every character expectation of its limit equals
`exp(-t r(k))`. The proof uses compactness of probability measures on the
compact torus, weak continuity of bounded complex character integrals, and
the exact density-level Fourier identity from1623. It does not insert the
desired Fourier moments as an assumption on the limit measure.

The key premise, existence of a common normalized approximate-square
sequence for **all** wave numbers, remains unproved. A uniform finite-box
sequence on `Z³` should have the required autocorrelation/overlap ratio, but
its finite-support combinatorics and limit have not yet been formalized.
There is consequently no unconditional heat transition law, convolution
semigroup, Markov kernel or stochastic process from this theorem. Uniqueness
of a measure from its characters also remains to be verified for subsequent
composition laws. This reduction is an application of classical compactness
and harmonic analysis, not a novelty claim. Full6874-job root build and
complete52119-declaration transitive axiom audit passed with only propext,
Classical.choice and Quot.sound. The unabridged public type, full proof,
three independent specializations and three local instances were reviewed.
Source/config/archive integrity is checked against the previous exact
checkpoint; ResearchSources is unchanged. Exact Git receipt and private
dual-ref verification follow.

## Checkpoint1625 — unconditional physical torus heat probability law (October27,2026)

The conditional harmonic premise from1624 is now discharged in
`Foundation/PhysicalHeatFiniteBox.lean`. `cube` is the finite product of three
integer intervals and `card_cube` gives exactly `(2n+1)^3` modes.
`cubePolynomial_square_coeff` identifies the unnormalized square Fourier
coefficient with the number of frequencies retained under translation by
the test wave number. `normalizedCube_energy` proves exact unit energy, not
an asymptotic normalization. For each fixed `k`, `cube_translate_inner`
bounds the overlap below by a smaller cube of radius `n-radius(k)`; the
normalized lower ratio tends to one. `normalizedCube_coeff_tendsto` therefore
proves the full simultaneous Fourier approximate identity required by1624.

`exists_physical_heat_law` consequently constructs, for EVERY nonnegative
rate `r : Z³ → ℝ≥0` whose real cast is a covariance symbol and with `r(0)=0`,
and EVERY nonnegative time, an ACTUAL probability measure on the compact
three-torus whose character expectation at `k` is exactly `exp(-t r(k))`.
This is an unconditional measure-existence theorem, not merely an L²
operator identity or a sequence of auxiliary densities. The measure is
obtained through compactness and is not yet selected canonically. Fourier
uniqueness, convolution composition, translation kernels, consistent
finite-dimensional distributions and stochastic path regularity remain open.
No actual process, curvature inequality or entropy theorem is inferred.

The mathematical measure-existence principle is classical (Schoenberg and
Herglotz/Bochner); this checkpoint is a verified realization inside the
Stardust physical semigroup framework, with no classical novelty claim.
Full6875-job root build and complete52152-declaration transitive axiom audit
passed with only propext, Classical.choice and Quot.sound. All21 unabridged
public types,17 full proofs,4 definitions and5 independent checks were
reviewed. Source2695/config3/archive113 hashes matched. Original
ResearchSources bytes remain unchanged. Exact Git receipt and private
dual-ref verification follow.

## Checkpoint1626 — uniqueness of the physical torus heat law (October27,2026)

`Foundation/PhysicalHeatLawUnique.lean` proves that a probability measure on
the compact three-torus is determined by every complex Fourier-character
moment. The proof makes integration against each measure a bounded complex
linear functional on continuous functions (norm at most one), uses the verified
Stone--Weierstrass density of Fourier characters, then extends equality to
bounded real continuous functions and applies finite Borel-measure uniqueness.
There is no finite-frequency truncation or formal Fourier inversion assumption.

`physical_heat_law_unique` applies this result to two candidate laws at the
same symbol and time. `exists_unique_physical_heat_law` combines it with the
actual existence theorem from1625. Hence each admissible multiplier now has
a **unique actual probability law**. This does not yet prove convolution
composition, a Markov transition kernel, consistent finite-dimensional laws,
or sample-path properties. Those are the next realization obligations. The
argument is classical compact harmonic analysis; no novelty is claimed.
The full6876-job root build, complete52155-declaration transitive axiom audit,
three unabridged public types, three full proofs, one private definition and
three independent specializations passed. Source/config/archive hashes are
checked against the previous exact checkpoint before commit and backup.

## Checkpoint1627 — physical torus convolution semigroup (October27,2026)

`Foundation/PhysicalHeatConvolution.lean` defines the canonical probability
law `heatLaw r hr hr0 t` by the unique existence theorem from1626. Fourier
characters multiply under torus addition, and `character_convolution` proves
the exact product rule for their actual integrals against two probability
measures. Combining that rule with the exponential multiplier law and Fourier
uniqueness proves `heatLaw_conv`: the measure convolution at times `s,t`
equals the law at `s+t`. `heatLaw_zero` identifies the zero-time law with the
Dirac mass at the torus origin. These are genuine measure identities, not
only L² multiplier equations.

The family is thus a probability convolution semigroup. Weak continuity in
time, translation transition kernels, consistent finite-dimensional laws,
and a process with any path regularity are still separate obligations. The
result is a classical semigroup construction specialized to the verified
physical symbol criterion; no novelty or Bakry curvature assertion follows.
The full6877-job root build and complete52160-declaration whitelist-only
transitive axiom audit passed. All five unabridged public types, four proofs,
one definition, two private supporting proofs and four independent tests were
reviewed. Source/config/archive integrity is checked against1626 before the
exact commit, receipt and dual PRIVATE backup.

## Checkpoint1628 — weak continuity of the physical heat laws (October27,2026)

`Foundation/PhysicalHeatWeakContinuity.lean` proves that each complex torus
Fourier-character integral is continuous in Mathlib's weak topology on
probability measures. `heatLaw_continuous` then proves continuity of the
entire actual law family `t ↦ heatLaw r hr hr0 t` for every admissible symbol.
The proof uses compactness of probability measures on the compact torus:
every candidate cluster law inherits the continuously varying Fourier
moments, so uniqueness from1626 identifies it with the law at the target
time. This establishes weak convergence for all bounded continuous tests,
not merely pointwise convergence of character moments.

`heatLaw_tendsto_dirac_zero` specializes this to weak convergence to the
Dirac mass at the origin as time decreases to zero. Combined with the
convolution law from1627, this is a weakly continuous probability convolution
semigroup. A transition kernel, consistent path-space laws, and any path
regularity or generator-domain identification remain open. Weak convergence
to a point mass is a distributional statement, not an actual process theorem.
No Bakry curvature or stochastic-calculus conclusion is inferred.
The full6878-job root build and complete52164-declaration whitelist-only
transitive axiom audit passed. All three unabridged public types and proofs,
four independent specializations, and source/config/archive integrity were
reviewed before exact commit, receipt and dual PRIVATE backup.

## Checkpoint1629 — actual physical heat Markov kernel (October27,2026)

`Foundation/PhysicalHeatKernel.lean` constructs `heatKernel r hr hr0 t` by
coupling the identity kernel with the constant verified heat law and mapping
the pair through torus addition. This is a genuine measurable Markov kernel:
`heatKernel_apply` identifies its value at `x` with the pushforward of the
actual probability law under `y ↦ x+y`, and the `IsMarkovKernel` instance
establishes normalization for every starting point.

`heatKernel_character` proves the translated Fourier-moment formula by an
actual integral against that kernel. `heatKernel_comp` then proves exact
Chapman--Kolmogorov composition at all nonnegative times, using the kernel
integral theorem, moment multiplication and the Fourier measure-uniqueness
theorem from1626. `heatKernel_zero` is the identity kernel. The theorem is
about actual transition measures, beyond the previous law-level convolution
statement. It still does not construct a stochastic process on a path space,
prove finite-dimensional consistency in Lean, identify a generator domain,
or establish path regularity. No Bakry curvature assertion follows.
The full6879-job root build and complete52171-declaration whitelist-only
transitive axiom audit passed. All six unabridged public types, four theorem
proofs, one definition, the Markov instance proof, private character proof
and five independent specializations were reviewed. Source/config/archive
integrity is checked before exact commit, receipt and dual PRIVATE backup.

## Checkpoint1630 — actual fixed-step physical heat chain (October27,2026)

`Foundation/PhysicalHeatChain.lean` composes the actual Markov heat kernel
with the Ionescu--Tulcea trajectory theorem. For every fixed nonnegative
step `δ` and initial torus point `x₀`, `chainLaw` is a genuine probability
measure on countable torus paths. `chainLaw_initial` identifies the exact
time-zero marginal with `dirac x₀`. `chainLaw_condDistrib` identifies the
regular conditional law of coordinate `n+1` given every coordinate through
`n` with the physical heat transition kernel at step `δ`, almost everywhere
under the actual finite-past law. The `stepKernel` construction explicitly
selects the last observed coordinate; zero step is independently tested to
give the identity transition.

This is a real stochastic process on a **fixed discrete grid**. It is not a
continuous-time path-space construction: consistency across distinct grids,
stochastic continuity of a single realized process, cadlag/continuous paths,
and generator-domain identification remain open. Weak continuity of the laws
and Chapman--Kolmogorov are available but do not alone constitute those path
theorems. There is no Bakry curvature or covariance conclusion from this
construction by itself. The method is the classical Ionescu--Tulcea theorem
applied to the verified physical heat kernel; no novelty is claimed.
The full6880-job root build and complete52180-declaration whitelist-only
transitive axiom audit passed. All seven unabridged public types, three theorem
proofs, two definitions, two instance proofs, and four independent checks were
reviewed. Source/configuration and all113 archive hashes matched the baseline.

## Checkpoint1631 — exact marginals and operator characters on every grid point

`Foundation/PhysicalHeatChainMarginals.lean` upgrades the fixed-step process
from a transition-law existence result to a precise process/operator bridge.
`chainLaw_next` extracts from the Ionescu--Tulcea joint law the actual marginal
recurrence: the distribution of coordinate `n+1` is the heat kernel applied to
the distribution of coordinate `n`. It uses the joint past/next-coordinate
identity, projection of the kernel composition, and the fact that the kernel
depends only on the latest past coordinate. `chainLaw_marginal` then uses
Chapman--Kolmogorov to prove that the actual `n`th coordinate has law
`heatKernel ((n:ℝ≥0)*δ) x₀` for every natural `n`. `chainLaw_character`
integrates Fourier characters against this actual path law, obtaining the
same `exp(-nδ r(k))` multiplier as the verified physical operator semigroup.
The direct one-step marginal and character identities are also recorded.

These are exact grid-time stochastic laws, not continuous-time realizations.
The current Mathlib audit located `IsProjectiveMeasureFamily` and its additive
cylinder content, and the countable-index Ionescu--Tulcea extension used here;
it did not identify a ready-made general-index extension theorem or a path
regularity theorem applicable to this compact-torus family. A continuous-time
process would still require consistent finite-dimensional laws over arbitrary
times and an extension/construction; cadlag or continuous paths additionally
need quantitative increment bounds or a separate regularity argument. This
does not supply curvature or a spectral gap. No novelty is claimed.
The full6881-job root build and complete52186-declaration whitelist-only
transitive axiom audit passed. All five unabridged public types and proofs,
four independent tests, and exact source/configuration/archive integrity were
reviewed before the commit and private backup.

## Checkpoint1632 — actual heat-chain covariance has Fourier Gamma derivative

`Foundation/PhysicalHeatChainGamma.lean` closes a process-level part of the
curvature--covariance correspondence. For the actual heat chain started at
the torus origin, the complex pairing of character increments
`(χ_{-k}(X₁)-1)(χ_l(X₁)-1)` has the exact finite-time expectation
`exp(-t r(k-l)) - exp(-t r(k)) - exp(-t r(l)) + 1`.
The second factor is the conjugate of `χ_{-l}(X₁)-1`, so this is a genuine
Hermitian increment-covariance pairing. The proof uses the actual one-step
path marginal, Fourier character multiplication, the heat-kernel integral
formula, and evenness derived from the verified covariance-symbol criterion.

`chainLaw_incrementPair_hasDerivWithinAt_zero` proves directly in Lean that
the **right derivative** at time zero of the real part of this actual
process pairing equals `2 * kernel r k l`, where `kernel` is the previously
verified Fourier Gamma covariance form `(r(k)+r(l)-r(l-k))/2`.
The source also proves the finite-time kernel pairing and the derivative of
its explicit real formula. The right-sided domain `Set.Ici 0` and the
`Real.toNNReal` time conversion are visible in the theorem type; no
negative-time process is postulated. Independent tests cover complex
conjugacy, zero-time pairing, diagonal variance and the right derivative.

This is a rigorous stochastic realization of the **algebraic Gamma kernel**
for admissible physical heat symbols. It does not establish positive
`Gamma₂ ≥ ρ Gamma`, a curvature-dimension estimate, a Poincare inequality,
or a new spectral gap. The construction is consistent with classical
Schoenberg/Levy-generator theory; no novelty claim is made. It also does
not establish a single continuous-time process or path regularity: each
nonnegative `t` here selects a fixed-step chain law.
The full6882-job root build and complete52191-declaration whitelist-only
transitive axiom audit passed. All four unabridged public theorem types and
proofs, the private evenness proof, four independent tests, and exact
source/configuration/archive integrity were reviewed before checkpoint closure.

## Checkpoint1633 — finite-time covariance symbol and process pairing

`Foundation/PhysicalHeatFiniteTimeCovariance.lean` proves that for every
normalized physical covariance symbol `r` and `t ≥ 0`, the transform
`φ_t(k) = 1 - exp(-t r(k))` is again a covariance symbol. The proof uses the
existing finite Schoenberg positive-definiteness theorem and the zero-sum
negative-energy criterion: the constant part cancels exactly, leaving the
negative of the positive heat-multiplier energy. This is a reusable
finite-time statement, not merely a derivative at zero.

The exact identity `2 kernel φ_t k l = exp(-t r(k-l)) - exp(-t r(k))
- exp(-t r(l)) + 1` is proved and identified with the corresponding complex
character-increment expectation under the **actual fixed-step heat-chain law**.
Consequently all finite matrices of these real Gamma kernels are positive
semidefinite; an independent Lean test checks this quantified matrix form.
Other independent tests cover frequency zero, time zero, and diagonal
variance. The transform and PSD mechanism are classical Schoenberg/compound-
Poisson mathematics; no novelty is claimed. The result supplies neither a
positive `Γ₂` curvature bound nor continuous-time paths, filtration, or a
spectral gap.

The full6883-job root build and complete52201-declaration whitelist-only
transitive axiom audit passed. All seven unabridged public types, six theorem
proofs, one definition and five independent tests were reviewed. Source,
configuration and all113 research-archive hashes match the prior baseline.

## Checkpoint1634 — finite-time covariance is not Loewner monotone

`Foundation/PhysicalHeatCovarianceNonmonotonicity.lean` gives a concrete
quadratic Brownian heat symbol on one torus coordinate, with frequencies
`1` and `-2`. At times `s = log 2` and `t = 2 log 2`, the anchored Gamma
matrices of `1 - exp(-s r)` and `1 - exp(-t r)` are individually PSD by
checkpoint1633, but their difference is **not** PSD. The witness weights
`(1,-2)` have exactly verified quadratic energy `-16897/131072` in the
difference. A public existential theorem packages the normalized admissible
rate, positive ordered times, and non-PSD two-by-two matrix.

This refutes a tempting strengthening of finite-time covariance positivity:
there is no general Loewner monotonicity in time. It does not refute the
earlier pointwise-in-time PSD theorem or assert negative Bakry curvature;
the standard quadratic heat generator itself supplies the counterexample.
The mechanism is that a heat transition can redistribute Fourier interference
among observed character combinations even while every time-slice covariance
remains positive. No novelty is claimed for this elementary spectral
phenomenon; the Lean declaration makes its exact hypothesis boundary usable.

The full6884-job root build and complete52221-declaration whitelist-only
transitive axiom audit passed. All12 unabridged public types, six theorem
proofs, six definitions, four private supporting proofs and six independent
checks were reviewed. Source/configuration and all113 archive hashes match
the previous checkpoint. Exact Git approval and private backup close it.

## Checkpoint1635 — sharp flat curvature on the quadratic Fourier core

`Foundation/PhysicalHeatFlatCurvature.lean` uses the actual Fourier
generator recursion `FiniteStableGamma.Core.gammaIter` and the already
verified general covariance-power positivity theorem. For the same
one-coordinate quadratic heat symbol as checkpoint1634, the second Gamma
iteration is real and nonnegative at every synthesis point for every finite
complex Fourier polynomial. The explicit Hermitian sine mode has
`Γ₁(f,f)(0)=4` and `Γ₂(f,f)(0)=0`. Thus no constant `ρ>0` can satisfy the
pointwise core inequality `Γ₂≥ρ Γ₁` for all real-valued Fourier inputs.

This is an exact **zero-curvature sharpness** result on the finite Fourier
core. It clarifies the preceding nonmonotonicity example: failure of
finite-time Loewner monotonicity does not imply negative `Γ₂`; here `Γ₂` is
nonnegative, while strictly positive curvature fails independently. A
spectral gap, if established through separate compact-torus estimates,
would also not imply a positive pointwise curvature constant. This is
standard flat torus mathematics formalized by direct reuse of existing
Stardust declarations; no novelty is claimed. No closed generator domain
or continuous-time process curvature statement is inferred.

The full6885-job root build and complete52229-declaration whitelist-only
transitive axiom audit passed. All six unabridged public types, five theorem
proofs, one definition, three private definitions and four independent
checks were reviewed. Source/configuration and all113 archive hashes match
the previous checkpoint. Exact Git approval and private backup close it.
