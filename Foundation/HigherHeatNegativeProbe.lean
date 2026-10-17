import Foundation.HigherHeatCylindricalExpectation

/-! A bounded nonnegative witness detects the negative part of an actual signed heat law. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.HigherHeatNegativeProbe
open HigherHeatSignedLaws HigherHeatKernelMoments HigherHeatDyadicLaws
open HigherHeatCylindricalExpectation
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

theorem real_integral_density (f : α → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (g : α → ℝ) (hgm : Measurable g) (C : ℝ) (hg : ∀ x, ‖g x‖ ≤ C) :
    (∫ᵛ x, g x ∂•μ.withDensityᵥ f) = ∫ x, f x • g x ∂μ := by
  let P := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let N := μ.withDensity (fun x => ENNReal.ofReal (-f x))
  letI : IsFiniteMeasure P := isFiniteMeasure_withDensity_ofReal hf.2
  letI : IsFiniteMeasure N := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hiP : Integrable g P := Integrable.of_bound hgm.aestronglyMeasurable C (Eventually.of_forall hg)
  have hiN : Integrable g N := Integrable.of_bound hgm.aestronglyMeasurable C (Eventually.of_forall hg)
  have hvP : P.toSignedMeasure.Integrable g := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hiP
  have hvN : N.toSignedMeasure.Integrable g := by
    simpa only [VectorMeasure.Integrable,Measure.variation_toSignedMeasure] using hiN
  have hmn : Measurable (fun x => -f x) := hfm.neg
  have hrP := (integrable_withDensity_iff_integrable_smul₀' hfm.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hiP
  have hrN := (integrable_withDensity_iff_integrable_smul₀' hmn.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).mp hiN
  have hflip : (ContinuousLinearMap.lsmul ℝ ℝ).flip = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext x y
    simp [smul_eq_mul,mul_comm]
  change VectorMeasure.integral (μ.withDensityᵥ f) g (ContinuousLinearMap.lsmul ℝ ℝ) = _
  rw [← hflip]
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf]
  rw [VectorMeasure.integral_sub_vectorMeasure hvP hvN,
    VectorMeasure.integral_toSignedMeasure,VectorMeasure.integral_toSignedMeasure]
  change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) -
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (-f x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top),
    integral_withDensity_eq_integral_toReal_smul hmn.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top),← integral_sub hrP hrN]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 0 ≤ f x
  · rw [ENNReal.toReal_ofReal hx,ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr hx)]
    simp
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_ge hx),
      ENNReal.toReal_ofReal (neg_nonneg.mpr (le_of_not_ge hx))]
    simp


def probe (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => min (max (-(realKernel m hm T hT x)) 0) 1) (by fun_prop) 1 (by
      intro x
      rw [Real.norm_eq_abs,abs_of_nonneg (le_min (le_max_right _ _) (by norm_num))]
      exact min_le_right _ _)

theorem probe_nonneg (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    0 ≤ probe m hm T hT x := le_min (le_max_right _ _) (by norm_num)

theorem probe_le_one (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    probe m hm T hT x ≤ 1 := min_le_right _ _

theorem weighted_probe_integrable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Integrable (fun x : ℝ => realKernel m hm T hT x*probe m hm T hT x) := by
  apply (realKernel m hm T hT).integrable.norm.mono' (by unfold probe; fun_prop)
  filter_upwards with x
  rw [norm_mul,Real.norm_eq_abs (probe m hm T hT x),abs_of_nonneg (probe_nonneg m hm T hT x)]
  exact mul_le_of_le_one_right (norm_nonneg _) (probe_le_one m hm T hT x)

theorem weighted_probe_nonpos (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    realKernel m hm T hT x*probe m hm T hT x ≤ 0 := by
  by_cases hx : 0 ≤ realKernel m hm T hT x
  · simp [probe,max_eq_right (neg_nonpos.mpr hx)]
  · exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) (probe_nonneg m hm T hT x)

theorem negative_weighted_integral (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) :
    (∫ x : ℝ, realKernel m (by omega) T hT x*probe m (by omega) T hT x) < 0 := by
  have hi := weighted_probe_integrable m (by omega) T hT
  have hn := integral_nonpos (μ := volume) (weighted_probe_nonpos m (by omega) T hT)
  by_contra h
  have hz : (∫ x : ℝ, realKernel m (by omega) T hT x*probe m (by omega) T hT x)=0 :=
    le_antisymm hn (le_of_not_gt h)
  have hp := integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun x => neg_nonneg.mpr (weighted_probe_nonpos m (by omega) T hT x)) hi.neg
  have he : (fun x : ℝ => -(realKernel m (by omega) T hT x*probe m (by omega) T hT x)) =ᵐ[volume] 0 := by
    apply hp.mp
    rw [integral_neg,hz,neg_zero]
  apply not_nonnegative_ae m hm T hT
  filter_upwards [he] with x hx
  change 0 ≤ realKernel m (by omega) T hT x
  by_contra hneg
  have hk : realKernel m (by omega) T hT x < 0 := lt_of_not_ge hneg
  have hg : 0 < probe m (by omega) T hT x :=
    lt_min (lt_max_of_lt_left (neg_pos.mpr hk)) (by norm_num)
  have hprod := mul_neg_of_neg_of_pos hk hg
  change -(realKernel m (by omega) T hT x*probe m (by omega) T hT x)=0 at hx
  linarith

open HigherHeatCylinderFourier HigherHeatBlockCoarsening

def terminalIndex : Fin (gridSize 0) := ⟨0,by norm_num [gridSize]⟩

def terminalTest (f : ℝ →ᵇ ℝ) : Test 0 :=
  f.compContinuous ⟨fun y : Grid 0 => y terminalIndex,continuous_apply terminalIndex⟩

set_option backward.isDefEq.respectTransparency false in
theorem law_zero (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    law m hm T hT 0=incrementLaw m hm (fun _ : Fin 1 => T) (fun _ => hT) := by
  unfold HigherHeatDyadicLaws.law positionLaw configurationLaw
  simp only [gridSize,duration,Nat.cast_one,div_one]
  have hid : (linearImage (cumulativeMatrix 1) : (Fin 1 → ℝ) → (Fin 1 → ℝ))=id := by
    funext x i
    fin_cases i
    simp [linearImage,cumulativeMatrix]
  rw [hid,VectorMeasure.map_id]

set_option backward.isDefEq.respectTransparency false in
theorem terminal_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : ℝ →ᵇ ℝ) :
    expectation m hm T hT 0 (terminalTest f) = ∫ x : ℝ, realKernel m hm T hT x*f x := by
  change (∫ᵛ y : Grid 0, f (y terminalIndex) ∂•HigherHeatDyadicLaws.law m hm T hT 0) = _
  rw [law_zero]
  change (∫ᵛ y : Fin 1 → ℝ, f (y 0) ∂•incrementLaw m hm (fun _ : Fin 1 => T) (fun _ => hT)) = _
  have hdm : Measurable (incrementDensity m hm (fun _ : Fin 1 => T) (fun _ => hT)) := by
    unfold incrementDensity
    apply Finset.measurable_prod
    intro j _
    exact (realKernel m hm T hT).continuous.measurable.comp (measurable_pi_apply j)
  have hfm : Measurable (fun y : Fin 1 → ℝ => f (y 0)) :=
    f.continuous.measurable.comp (measurable_pi_apply 0)
  rw [incrementLaw,real_integral_density _ _ (incrementDensity_integrable m hm _ _) hdm
    (fun y : Fin 1 → ℝ => f (y 0)) hfm ‖f‖ (fun y => f.norm_coe_le_norm (y 0))]
  simp only [incrementDensity,Fin.prod_univ_one,smul_eq_mul]
  exact (measurePreserving_funUnique (volume : Measure ℝ) (Fin 1)).integral_comp'
    (fun x : ℝ => realKernel m hm T hT x*f x)

def negativeCylinder (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : Cylinder :=
  cylinderOf 0 (terminalTest (probe m hm T hT))

theorem negative_cylinder_expectation (m : ℕ) (hm : 2 ≤ m) (T : ℝ≥0) (hT : 0 < T) :
    cylindricalExpectation m (by omega) T hT (negativeCylinder m (by omega) T hT) < 0 := by
  rw [negativeCylinder,cylindricalExpectation_apply,terminal_expectation]
  exact negative_weighted_integral m hm T hT

theorem terminal_probe_nonnegative (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (y : Grid 0) :
    0 ≤ terminalTest (probe m hm T hT) y := probe_nonneg m hm T hT (y terminalIndex)

end OperatorDerivativeRewrite.Foundation.HigherHeatNegativeProbe
