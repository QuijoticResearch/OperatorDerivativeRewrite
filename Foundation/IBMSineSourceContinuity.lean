import Foundation.IBMSineSourceIntegral
import Foundation.HigherLpUniformIntegrability

/-! Strong L2 time continuity from actual continuous coefficient paths and
uniform fourth moments. No independence of IBM increments is used. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSineSourceContinuity
open InfiniteGaussian IBMConstructedSources IBMSineSourceField
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : MeasurableSpace CoefficientSpace := borel CoefficientSpace
local instance : BorelSpace CoefficientSpace := ⟨rfl⟩
attribute [local irreducible] clockPath ibmValue

theorem direction_norm_sq (r : ℝ) : ‖direction r‖ ^ 2 = |r| := by
  have h := IBMRandomTimeHilbert.sourceScenery_norm_sq r
  simpa only [direction, IBMContinuousScenery.sourceScenery, LinearIsometry.norm_map] using h

theorem value_four_bound (t : ℝ) (p : IBMSourceLaws.JointSample) :
    ‖value t p‖ ^ 4 ≤ (clockPath p.1 t.toNNReal) ^ 2 := by
  have hn : ‖value t p‖ ≤ ‖direction |clockPath p.1 t.toNNReal|‖ := by
    change ‖Real.cos _ • direction _‖ ≤ _
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (norm_nonneg _)).trans_eq (one_mul _)
  calc
    _ ≤ ‖direction |clockPath p.1 t.toNNReal|‖ ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hn 4
    _ = (‖direction |clockPath p.1 t.toNNReal|‖ ^ 2) ^ 2 := by ring
    _ = _ := by rw [direction_norm_sq]; simp only [abs_abs, sq_abs]

theorem clock_square_integrable (t : ℝ≥0) :
    Integrable (fun Y => (clockPath Y t) ^ 2) gaussianProduct := by
  have hm : MemLp (fun Y => clockPath Y t) 2 gaussianProduct :=
    (GaussianTimeProcess.process_memLp t 2 (by simp)).ae_eq (clockPath_coordinate_ae t).symm
  simpa only [Real.norm_eq_abs, sq_abs] using hm.integrable_norm_pow'

theorem clock_square_integral (t : ℝ≥0) :
    (∫ Y, (clockPath Y t) ^ 2 ∂gaussianProduct) = (t : ℝ) := by
  have he : (fun Y => (clockPath Y t) ^ 2) =ᵐ[gaussianProduct]
      fun Y => (GaussianTimeProcess.process t Y) ^ 2 := (clockPath_coordinate_ae t).fun_comp (fun x => x ^ 2)
  rw [integral_congr_ae he]
  simpa only [pow_two, min_self] using GaussianTimeProcess.process_product_integral t t

theorem value_four_integrable (t : ℝ) :
    Integrable (fun p => ‖value t p‖ ^ 4) IBMSourceLaws.jointMeasure := by
  apply ((clock_square_integrable t.toNNReal).comp_fst gaussianProduct).mono'
    ((value_jointly_measurable.comp (measurable_const.prodMk measurable_id)).norm.pow_const 4).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact value_four_bound t p

theorem value_four_moment (t : ℝ) :
    (∫ p, ‖value t p‖ ^ 4 ∂IBMSourceLaws.jointMeasure) ≤ (t.toNNReal : ℝ) := by
  calc
    _ ≤ ∫ p : IBMSourceLaws.JointSample, (clockPath p.1 t.toNNReal) ^ 2 ∂IBMSourceLaws.jointMeasure :=
      integral_mono (value_four_integrable t) ((clock_square_integrable t.toNNReal).comp_fst gaussianProduct)
        (value_four_bound t)
    _ = _ := by
      change (∫ p, (clockPath p.1 t.toNNReal) ^ 2 ∂gaussianProduct.prod gaussianProduct) = _
      calc
        _ = gaussianProduct.real univ • (∫ Y, (clockPath Y t.toNNReal) ^ 2 ∂gaussianProduct) :=
          integral_fun_fst (fun Y => (clockPath Y t.toNNReal) ^ 2)
        _ = _ := by simpa using clock_square_integral t.toNNReal

theorem value_memLp_four (t : ℝ) : MemLp (value t) 4 IBMSourceLaws.jointMeasure := by
  apply (integrable_norm_rpow_iff
    ((value_jointly_measurable.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)).mp
  simpa using value_four_integrable t

theorem value_four_norm_bound (t : ℝ) (T : ℝ≥0) (ht : t.toNNReal ≤ T) :
    eLpNorm (value t) 4 IBMSourceLaws.jointMeasure ≤ ENNReal.ofReal ((T : ℝ) ^ (1 / 4 : ℝ)) := by
  rw [MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp) (value_memLp_four t)]
  norm_num only [ENNReal.toReal_ofNat]
  have hpow (x : ℝ) : x ^ (4 : ℝ) = x ^ (4 : ℕ) := Real.rpow_natCast x 4
  simp_rw [hpow]
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow (integral_nonneg fun p => by positivity)
    ((value_four_moment t).trans ht) (by norm_num)

theorem value_continuous (p : IBMSourceLaws.JointSample) : Continuous (fun t => value t p) := by
  exact (Real.continuous_cos.comp ((ibmValue_continuous (p.2, p.1)).comp continuous_real_toNNReal)).smul
    (direction_continuous.comp (continuous_abs.comp ((clockPath p.1).continuous.comp continuous_real_toNNReal)))

theorem flat_continuous : Continuous flat := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  obtain ⟨R, hR⟩ := hu.cauchySeq.isBounded_range.exists_norm_le
  let T : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
  have hb (n : ℕ) : (u n).toNNReal ≤ T :=
    Real.toNNReal_le_iff_le_coe.mpr ((le_abs_self _).trans ((hR _ (mem_range_self n)).trans (le_max_left _ _)))
  have hf (n : ℕ) : AEStronglyMeasurable (value (u n)) IBMSourceLaws.jointMeasure :=
    (value_memLp (u n)).aestronglyMeasurable
  have ha : ∀ᵐ p ∂IBMSourceLaws.jointMeasure, Tendsto (fun n => value (u n) p) atTop (𝓝 (value t p)) :=
    ae_of_all _ fun p => (value_continuous p).continuousAt.tendsto.comp hu
  obtain ⟨hg, ht⟩ := HigherLpUniformIntegrability.finite_higher_ae_Lp_convergence
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) < 4) (by simp : (4 : ℝ≥0∞) ≠ ∞)
    (fun n => value (u n)) (value t) hf (ENNReal.ofReal ((T : ℝ) ^ (1 / 4 : ℝ))) (by simp)
      (fun n => value_four_norm_bound (u n) T (hb n)) ha
  have hc := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => value (u n))
    (fun n => value_memLp (u n)) (value t) (value_memLp t)).mpr ht
  have he (s : ℝ) : (value_memLp s).toLp (value s) = flat s :=
    Lp.ext ((value_memLp s).coeFn_toLp.trans (flat_ae s).symm)
  simpa only [he, Function.comp_def] using hc

end OperatorDerivativeRewrite.Foundation.IBMSineSourceContinuity
