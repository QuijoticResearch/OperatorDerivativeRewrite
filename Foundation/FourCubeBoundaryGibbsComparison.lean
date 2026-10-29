import Foundation.FourCubeScaledBoundaryControl

/-! Actual perturbed Gibbs probability measures and comparison with the reference law. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.FourCubeBoundaryGibbsComparison
open QuaternionSU2Representation OneSidedCapComplex FourCubeIntegratedCubic FourCubePinnedHaar
open FourCubePinnedCoercivity FourCubePinnedConcentration FourCubeBoundaryCoercivity

def source (b : Boundary → SU2) (U : PinnedState) : ℝ := -perturbedAction b U/144

theorem source_measurable (b : Boundary → SU2) : Measurable (source b) :=
  (perturbedAction_measurable b).neg.div_const _

theorem source_bound (b : Boundary → SU2) (U : PinnedState) : |source b U| ≤ 1 := by
  have hh := FourCubeHaarParity.fullAction_bounds (fill b (fillPole 1 U))
  change 0 ≤ perturbedAction b U ∧ perturbedAction b U ≤ 144 at hh
  rw [abs_le]
  constructor <;> unfold source <;> linarith

def law (β : ℝ) (b : Boundary → SU2) : Measure PinnedState :=
  BoundedExponentialTiltResponse.tiltedMeasure pinnedHaar (source b) (144*β)

instance law_probability (β : ℝ) (b : Boundary → SU2) : IsProbabilityMeasure (law β b) :=
  BoundedExponentialTiltResponse.tiltedMeasure_probability pinnedHaar (source b)
    (source_measurable b) (source_bound b) (144*β)

theorem law_identity (β : ℝ) : law β (fun _ => (1 : SU2))=gibbs β := rfl

theorem tilted_partition_eq (β : ℝ) (b : Boundary → SU2) :
    BoundedExponentialTiltResponse.partition pinnedHaar (source b) (144*β)=pinnedPartition β b := by
  unfold BoundedExponentialTiltResponse.partition BoundedExponentialTiltResponse.weighted
  change (∫ U,1*Real.exp ((144*β)*source b U) ∂pinnedHaar)=_
  unfold pinnedPartition weight
  apply integral_congr_ae
  filter_upwards with U
  simp only [one_mul]
  congr 1
  unfold source perturbedAction boundaryAction
  ring

def density (β : ℝ) (b : Boundary → SU2) (U : PinnedState) : ℝ :=
  Real.exp (-β*perturbedAction b U)/pinnedPartition β b

theorem density_nonneg (β : ℝ) (b : Boundary → SU2) (U : PinnedState) : 0 ≤ density β b U :=
  div_nonneg (Real.exp_pos _).le (pinnedPartition_positive β b).le

theorem density_formula (β : ℝ) (b : Boundary → SU2) (U : PinnedState) :
    BoundedExponentialTiltResponse.density pinnedHaar (source b) (144*β) U=density β b U := by
  rw [BoundedExponentialTiltResponse.density,tilted_partition_eq]
  unfold density
  congr 1
  congr 1
  unfold source
  ring

theorem law_withDensity (β : ℝ) (b : Boundary → SU2) :
    law β b=pinnedHaar.withDensity (fun U => ENNReal.ofReal (density β b U)) := by
  unfold law BoundedExponentialTiltResponse.tiltedMeasure
  simp_rw [density_formula]

theorem law_integral (β : ℝ) (b : Boundary → SU2) (f : PinnedState → ℝ) :
    (∫ U,f U ∂law β b)=(∫ U,f U*Real.exp (-β*perturbedAction b U) ∂pinnedHaar)/pinnedPartition β b := by
  rw [law,BoundedExponentialTiltResponse.tilted_integral pinnedHaar (source b) f
    (source_measurable b) (source_bound b),BoundedExponentialTiltResponse.expectation,
    tilted_partition_eq]
  unfold BoundedExponentialTiltResponse.weighted
  congr 1
  apply integral_congr_ae
  filter_upwards with U
  congr 2
  unfold source
  ring

def comparisonCoefficient (β : ℝ) (b : Boundary → SU2) : ℝ :=
  Real.exp (4*β*boundaryCost b)*(normalizer (β/3)/normalizer (3*β))

theorem comparisonCoefficient_positive (β : ℝ) (b : Boundary → SU2) :
    0 < comparisonCoefficient β b :=
  mul_pos (Real.exp_pos _) (div_pos (normalizer_positive _) (normalizer_positive _))

theorem density_comparison (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) (U : PinnedState) :
    density β b U ≤ comparisonCoefficient β b*density (β/3) (fun _ => (1 : SU2)) U := by
  have hd := mul_pos (Real.exp_pos (-3*β*boundaryCost b)) (normalizer_positive (3*β))
  have hh := div_le_div₀
    (mul_nonneg (Real.exp_pos (β*boundaryCost b)).le (Real.exp_pos (-(β/3)*pinnedAction U)).le)
    (boltzmann_upper β hβ b U) hd (pinnedPartition_lower β hβ b)
  have he : Real.exp (β*boundaryCost b)/Real.exp (-3*β*boundaryCost b)=
      Real.exp (4*β*boundaryCost b) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  change density β b U ≤ _ at hh
  apply hh.trans_eq
  calc
    _ = (Real.exp (β*boundaryCost b)/Real.exp (-3*β*boundaryCost b))*
        (normalizer (β/3)/normalizer (3*β))*
        (Real.exp (-(β/3)*pinnedAction U)/normalizer (β/3)) := by
      field_simp [(normalizer_positive (β/3)).ne',
        (normalizer_positive (3*β)).ne',Real.exp_ne_zero]
    _ = _ := by rw [he]; rfl

/-- Domination of actual measures, with no cutoff or observable restriction. -/
theorem law_le_reference (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) :
    law β b ≤ ENNReal.ofReal (comparisonCoefficient β b) • gibbs (β/3) := by
  rw [← law_identity (β/3),law_withDensity,law_withDensity]
  rw [← withDensity_smul' (ENNReal.ofReal (comparisonCoefficient β b))
    (fun U : PinnedState => ENNReal.ofReal (density (β/3) (fun _ => (1 : SU2)) U))
    ENNReal.ofReal_ne_top]
  apply withDensity_mono
  filter_upwards with U
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [← ENNReal.ofReal_mul (comparisonCoefficient_positive β b).le]
  exact ENNReal.ofReal_le_ofReal (density_comparison β hβ b U)

theorem law_real_le_reference (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) (A : Set PinnedState) :
    (law β b).real A ≤ comparisonCoefficient β b*(gibbs (β/3)).real A := by
  have hh := law_le_reference β hβ b A
  have ht : (ENNReal.ofReal (comparisonCoefficient β b) • gibbs (β/3)) A ≠ ∞ := by
    simp [Measure.smul_apply,ENNReal.mul_ne_top]
  have hr := ENNReal.toReal_mono ht hh
  simpa only [Measure.real,Measure.smul_apply,smul_eq_mul,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (comparisonCoefficient_positive β b).le] using hr

/-- A full probability-measure domination factor cannot be a strict contraction. -/
theorem comparisonCoefficient_ge_one (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2) :
    1 ≤ comparisonCoefficient β b := by
  simpa only [probReal_univ,mul_one] using law_real_le_reference β hβ b Set.univ

theorem bounded_test_integrable (β : ℝ) (b : Boundary → SU2) (f : PinnedState → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ U, |f U| ≤ M) : Integrable f (law β b) := by
  apply (integrable_const M).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using hb U)

theorem bounded_setIntegral_bound (β : ℝ) (b : Boundary → SU2) (A : Set PinnedState)
    (hA : MeasurableSet A) (f : PinnedState → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ U, |f U| ≤ M) :
    |∫ U in A,f U ∂law β b| ≤ M*(law β b).real A := by
  have hi := bounded_test_integrable β b f hf M hb
  calc
    _ = ‖∫ U in A,f U ∂law β b‖ := by rw [Real.norm_eq_abs]
    _ ≤ ∫ U in A,‖f U‖ ∂law β b := norm_integral_le_integral_norm f
    _ ≤ ∫ U in A,M ∂law β b :=
      setIntegral_mono_on hi.norm.integrableOn (integrable_const M).integrableOn hA
        (fun U _ => by simpa only [Real.norm_eq_abs] using hb U)
    _ = _ := by simp only [setIntegral_const,smul_eq_mul,mul_comm]

end OperatorDerivativeRewrite.Foundation.FourCubeBoundaryGibbsComparison
