import Foundation.IBMFoldedTransitionBound

/-! Earlier-time bounded weights in the actual Gaussian clock transition
estimate. All law transport and product integrability are discharged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMEarlierWeightedOverlap
open InfiniteGaussian IBMFoldedTransitionBound

theorem increment_overlap_le (n m : ℕ) (a : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∫ b, overlap n m |a| |a+b| ∂gaussianReal 0 v) ≤ 2*peak v := by
  have hl := gaussianReal_const_add (HasLaw.id (μ := gaussianReal 0 v)) a
  have hc : Continuous (fun y : ℝ => overlap n m |a| |y|) :=
    (overlap_continuous n m).comp (continuous_const.prodMk continuous_abs)
  have heq := hl.integral_comp hc.aestronglyMeasurable
  simp only [zero_add, Function.comp_def, id_eq] at heq
  rw [heq]
  exact overlap_average_le n m |a| a hv

theorem weight_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (w : ℝ → ℝ)
    (hw : Measurable w) (h0 : ∀ a, 0 ≤ w a) (h1 : ∀ a, w a ≤ 1) : Integrable w μ :=
  Integrable.of_bound hw.aestronglyMeasurable 1
    (ae_of_all _ fun a => by simpa only [Real.norm_of_nonneg (h0 a)] using h1 a)

theorem product_integrable (n m : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (v : ℝ≥0) (w : ℝ → ℝ) (hw : Measurable w)
    (h0 : ∀ a, 0 ≤ w a) (h1 : ∀ a, w a ≤ 1) :
    Integrable (fun p : ℝ × ℝ => w p.1*overlap n m |p.1| |p.1+p.2|)
      (μ.prod (gaussianReal 0 v)) := by
  obtain ⟨M,hM0,hM⟩ := overlap_bounded n m
  have hF : Measurable (fun p : ℝ × ℝ => w p.1*overlap n m |p.1| |p.1+p.2|) :=
    (hw.comp measurable_fst).mul (((overlap_continuous n m).comp
      (continuous_fst.abs.prodMk (continuous_fst.add continuous_snd).abs)).measurable)
  apply Integrable.of_bound hF.aestronglyMeasurable M
  exact ae_of_all _ fun p => by
    rw [Real.norm_of_nonneg (mul_nonneg (h0 _) (overlap_nonneg _ _ _ _))]
    exact (mul_le_mul (h1 _) (hM _ _) (overlap_nonneg _ _ _ _) zero_le_one).trans_eq (one_mul _)

/-- Genuine weighted transition bound for any finite earlier marginal. -/
theorem product_weighted_le (n m : ℕ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    {v : ℝ≥0} (hv : v ≠ 0) (w : ℝ → ℝ) (hw : Measurable w)
    (h0 : ∀ a, 0 ≤ w a) (h1 : ∀ a, w a ≤ 1) :
    (∫ p : ℝ × ℝ, w p.1*overlap n m |p.1| |p.1+p.2| ∂μ.prod (gaussianReal 0 v)) ≤
      2*peak v*(∫ a, w a ∂μ) := by
  rw [integral_prod _ (product_integrable n m μ v w hw h0 h1)]
  simp_rw [integral_const_mul]
  calc
    _ ≤ ∫ a, w a*(2*peak v) ∂μ := by
      apply integral_mono_of_nonneg
        (ae_of_all _ fun a => mul_nonneg (h0 a)
          (integral_nonneg fun b => overlap_nonneg _ _ _ _))
        ((weight_integrable μ w hw h0 h1).mul_const _)
      exact ae_of_all _ fun a => mul_le_mul_of_nonneg_left (increment_overlap_le n m a hv) (h0 a)
    _ = _ := by rw [integral_mul_const]; ring

/-- The earlier weight remains correlated with the ACTUAL clock state; the
later increment is integrated using its proved independent joint law. -/
theorem process_weighted_le (n m : ℕ) (s t : ℝ≥0) (hst : s < t)
    (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ a, 0 ≤ w a) (h1 : ∀ a, w a ≤ 1) :
    (∫ ω, w (GaussianTimeProcess.process s ω)*
      overlap n m |GaussianTimeProcess.process s ω| |GaussianTimeProcess.process t ω|
        ∂gaussianProduct) ≤ 2*peak (nndist (t : ℝ) (s : ℝ))*
          (∫ ω, w (GaussianTimeProcess.process s ω) ∂gaussianProduct) := by
  open GaussianTimeProcess in
  have hind : IndepFun (process s) (fun ω => process t ω-process s ω) gaussianProduct := by
    apply (process_disjoint_increments_independent 0 s s t (by positivity) le_rfl hst.le).congr
      ?_ (Filter.EventuallyEq.rfl)
    filter_upwards [process_zero_ae] with ω hω
    simp [hω]
  have hp := hind.hasLaw_prod (GaussianTimeProcess.process_hasLaw s)
    (GaussianTimeProcess.process_increment_hasLaw s t)
  let v : ℝ≥0 := nndist (t : ℝ) (s : ℝ)
  have hv : v ≠ 0 := by simpa [v] using (ne_of_gt hst)
  let F : ℝ × ℝ → ℝ := fun p => w p.1*overlap n m |p.1| |p.1+p.2|
  have hF : Measurable F := (hw.comp measurable_fst).mul
    (((overlap_continuous n m).comp
      (continuous_fst.abs.prodMk (continuous_fst.add continuous_snd).abs)).measurable)
  have he : (∫ ω, w (GaussianTimeProcess.process s ω)*overlap n m
      |GaussianTimeProcess.process s ω| |GaussianTimeProcess.process t ω| ∂gaussianProduct) =
        ∫ p, F p ∂(gaussianReal 0 s).prod (gaussianReal 0 v) := by
    convert hp.integral_comp hF.aestronglyMeasurable using 1
    congr 1
    funext ω
    simp [F]
  have hm := (GaussianTimeProcess.process_hasLaw s).integral_comp hw.aestronglyMeasurable
  simp only [Function.comp_def] at hm
  rw [he, hm]
  exact product_weighted_le n m (gaussianReal 0 s) hv w hw h0 h1

theorem clockPath_weighted_le (n m : ℕ) (s t : ℝ≥0) (hst : s < t)
    (w : ℝ → ℝ) (hw : Measurable w) (h0 : ∀ a, 0 ≤ w a) (h1 : ∀ a, w a ≤ 1) :
    (∫ ω, w (IBMConstructedSources.clockPath ω s)*overlap n m
      |IBMConstructedSources.clockPath ω s| |IBMConstructedSources.clockPath ω t|
        ∂gaussianProduct) ≤
        2*peak (nndist (t : ℝ) (s : ℝ))*
          (∫ ω, w (IBMConstructedSources.clockPath ω s) ∂gaussianProduct) := by
  have he : (∫ ω, w (IBMConstructedSources.clockPath ω s)*overlap n m
      |IBMConstructedSources.clockPath ω s| |IBMConstructedSources.clockPath ω t|
        ∂gaussianProduct) =
        ∫ ω, w (GaussianTimeProcess.process s ω)*overlap n m
          |GaussianTimeProcess.process s ω| |GaussianTimeProcess.process t ω| ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [IBMConstructedSources.clockPath_coordinate_ae s,
      IBMConstructedSources.clockPath_coordinate_ae t] with ω hs ht
    rw [hs, ht]
  have hm : (∫ ω, w (IBMConstructedSources.clockPath ω s) ∂gaussianProduct) =
      ∫ ω, w (GaussianTimeProcess.process s ω) ∂gaussianProduct :=
    integral_congr_ae ((IBMConstructedSources.clockPath_coordinate_ae s).fun_comp w)
  rw [he, hm]
  exact process_weighted_le n m s t hst w hw h0 h1

end OperatorDerivativeRewrite.Foundation.IBMEarlierWeightedOverlap
