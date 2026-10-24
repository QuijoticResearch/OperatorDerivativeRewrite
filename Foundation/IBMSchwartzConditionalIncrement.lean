import Foundation.IBMSchwartzHeatIncrement
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-! Whole-history conditional increment covariance for the actual clock process,
with arbitrary past L2 scalar weights and full source GaussianL2 values. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzConditionalIncrement
open InfiniteGaussian GaussianTimeProcess GaussianBrownianConditionalTransition
open IBMSchwartzHalfHolderHeat IBMSchwartzHeatDerivative IBMSchwartzHeatSemigroup
open IBMSchwartzHeatIncrement
attribute [local irreducible] curve heatMean heatScore GaussianHalfHolderScore.score
  GaussianBoundedHeatDerivative.mean

private theorem bounded_weight_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (U : SampleSpace → ℝ) (F : SampleSpace → E)
    (hU : Integrable U gaussianProduct) (hF : AEStronglyMeasurable F gaussianProduct)
    (M : ℝ) (hb : ∀ Y, ‖F Y‖ ≤ M) :
    Integrable (fun Y => U Y • F Y) gaussianProduct := by
  apply (hU.norm.mul_const M).mono' (hU.aestronglyMeasurable.smul hF)
  exact Filter.Eventually.of_forall fun Y => by
    change ‖U Y • F Y‖ ≤ ‖U Y‖*M
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hb Y) (norm_nonneg _)

theorem increment_memLp (S R : ℝ≥0) :
    MemLp (fun Y => process R Y-process S Y) 2 gaussianProduct :=
  (process_memLp R 2 (by norm_num)).sub (process_memLp S 2 (by norm_num))

theorem increment_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R v : ℝ≥0) :
    Integrable (fun Y => (process R Y-process S Y) • heatMean g a (process R Y) v)
      gaussianProduct := by
  apply bounded_weight_integrable _ _ ((increment_memLp S R).integrable (by norm_num))
    _ (SchwartzMap.seminorm ℝ 0 0 g) (fun Y => heatMean_bound g a _ _)
  exact ((heatMean_continuous g a).stronglyMeasurable.comp_measurable
    ((process_stronglyMeasurable R).measurable.prodMk measurable_const)).aestronglyMeasurable

theorem conditional_increment (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R v : ℝ≥0)
    (hSR : S ≤ R) (hv : 0 < v) :
    gaussianProduct[
      fun Y => (process R Y-process S Y) • heatMean g a (process R Y) v |
        naturalFiltration S] =ᵐ[gaussianProduct]
      fun Y => ((R-S : ℝ≥0) : ℝ) •
        heatScore g a (process S Y) (((R-S)+v : ℝ≥0) : ℝ) := by
  let F : (Iic S → ℝ) × ℝ → GaussianL2 :=
    fun p => p.2 • heatMean g a (p.1 ⟨S,by simp⟩+p.2) v
  have hF : StronglyMeasurable F := by
    have hm : Measurable (fun p : (Iic S → ℝ) × ℝ =>
        (p.1 ⟨S,by simp⟩+p.2,(v : ℝ))) :=
      ((((measurable_pi_apply (⟨S,by simp⟩ : Iic S)).comp measurable_fst).add
        measurable_snd).prodMk measurable_const)
    simpa only [F,Function.comp_def,Pi.smul_def'] using measurable_snd.stronglyMeasurable.smul
      ((heatMean_continuous g a).stronglyMeasurable.comp_measurable hm)
  have he : (fun Y => F (past S Y,process R Y-process S Y)) =
      fun Y => (process R Y-process S Y) • heatMean g a (process R Y) v := by
    funext Y
    simp only [F,past,GaussianPredictableStep.pastProcess,add_sub_cancel]
  have h := IndependentInnovationConditioning.conditional_integral gaussianProduct
    (past S) (fun Y => process R Y-process S Y) (past_measurable S)
    ((process_stronglyMeasurable R).measurable.sub (process_stronglyMeasurable S).measurable)
    (past_increment_independent S R hSR) F hF (he.symm ▸ increment_integrable g a S R v)
  rw [he,← history_eq_comap S,(increment_law S R hSR).map_eq] at h
  filter_upwards [h] with Y hY
  exact hY.trans (mean_increment g a (process S Y) (R-S) v hv)

theorem weighted_increment (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R v : ℝ≥0)
    (hSR : S ≤ R) (hv : 0 < v) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ Y, V Y • ((process R Y-process S Y) • heatMean g a (process R Y) v)
      ∂gaussianProduct) =
    ((R-S : ℝ≥0) : ℝ) • ∫ Y,
      V Y • heatScore g a (process S Y) (((R-S)+v : ℝ≥0) : ℝ) ∂gaussianProduct := by
  have hp : Integrable (fun Y => V Y*(process R Y-process S Y)) gaussianProduct :=
    (Lp.memLp V).integrable_mul (increment_memLp S R)
  have hi : Integrable
      (fun Y => V Y • ((process R Y-process S Y) • heatMean g a (process R Y) v))
      gaussianProduct := by
    simpa only [smul_smul,Function.comp_def] using bounded_weight_integrable _ _ hp
      (((heatMean_continuous g a).stronglyMeasurable.comp_measurable
        ((process_stronglyMeasurable R).measurable.prodMk measurable_const)).aestronglyMeasurable)
      (SchwartzMap.seminorm ℝ 0 0 g) (fun Y => heatMean_bound g a _ _)
  have h := condExp_smul_of_aestronglyMeasurable_left hV hi
    (increment_integrable g a S R v)
  have he := conditional_increment g a S R v hSR hv
  calc
    _ = ∫ Y, gaussianProduct[
        fun Y => V Y • ((process R Y-process S Y) • heatMean g a (process R Y) v) |
          naturalFiltration S] Y ∂gaussianProduct := (integral_condExp (naturalFiltration.le S)).symm
    _ = ∫ Y, V Y • (((R-S : ℝ≥0) : ℝ) •
        heatScore g a (process S Y) (((R-S)+v : ℝ≥0) : ℝ)) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [h,he] with Y hY heY
      exact hY.trans (congrArg (fun w : GaussianL2 => V Y • w) heY)
    _ = _ := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun Y => smul_comm _ _ _

theorem weighted_terminal (g : SchwartzMap ℝ ℝ) (a : ℝ) (R T : ℝ≥0)
    (hRT : R ≤ T) (U : SampleSpace → ℝ) (hU : Integrable U gaussianProduct)
    (hm : AEStronglyMeasurable[naturalFiltration R] U gaussianProduct) :
    (∫ Y, U Y • curve g a (process T Y) ∂gaussianProduct) =
      ∫ Y, U Y • heatMean g a (process R Y) (T-R) ∂gaussianProduct := by
  have hf : AEStronglyMeasurable (fun Y => curve g a (process T Y)) gaussianProduct :=
    ((curve_continuous g a).stronglyMeasurable.comp_measurable
      (process_stronglyMeasurable T).measurable).aestronglyMeasurable
  have hi : Integrable (fun Y => curve g a (process T Y)) gaussianProduct :=
    (integrable_const (SchwartzMap.seminorm ℝ 0 0 g)).mono' hf
      (Filter.Eventually.of_forall fun Y => curve_bound g a _)
  have hp := bounded_weight_integrable U _ hU hf
    (SchwartzMap.seminorm ℝ 0 0 g) (fun Y => curve_bound g a _)
  have hc := condExp_smul_of_aestronglyMeasurable_left hm hp hi
  have hv := conditional_value g a R T hRT
  calc
    _ = ∫ Y, gaussianProduct[fun Y => U Y • curve g a (process T Y) |
        naturalFiltration R] Y ∂gaussianProduct := (integral_condExp (naturalFiltration.le R)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hc,hv] with Y hcY hvY
      exact hcY.trans (congrArg (fun w : GaussianL2 => U Y • w) hvY)

theorem terminal_step (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R T : ℝ≥0)
    (hSR : S ≤ R) (hRT : R < T) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ Y, (V Y*(process R Y-process S Y)) • curve g a (process T Y)
      ∂gaussianProduct) =
    ((R-S : ℝ≥0) : ℝ) • ∫ Y,
      V Y • heatScore g a (process S Y) (T-S) ∂gaussianProduct := by
  have hp : Integrable (fun Y => V Y*(process R Y-process S Y)) gaussianProduct :=
    (Lp.memLp V).integrable_mul (increment_memLp S R)
  have hm : AEStronglyMeasurable[naturalFiltration R]
      (fun Y => V Y*(process R Y-process S Y)) gaussianProduct :=
    (hV.mono (naturalFiltration.mono hSR)).mul
      ((process_stronglyAdapted R).sub
        ((process_stronglyAdapted S).mono (naturalFiltration.mono hSR))).aestronglyMeasurable
  rw [weighted_terminal g a R T hRT.le _ hp hm]
  have h := weighted_increment g a S R (T-R) hSR (tsub_pos_iff_lt.mpr hRT) V hV
  have he : (R-S)+(T-R) = T-S := by
    rw [add_comm]
    exact tsub_add_tsub_cancel hRT.le hSR
  simpa only [smul_smul,he,NNReal.coe_sub hRT.le,
    NNReal.coe_sub (hSR.trans hRT.le)] using h

theorem curve_increment (g : SchwartzMap ℝ ℝ) (a b : ℝ) (u : ℝ≥0) :
    (∫ x, x • curve g a (b+x) ∂gaussianReal 0 u) =
      (u : ℝ) • heatScore g a b u := by
  by_cases hu : u = 0
  · simp [hu]
  let σ : ℝ := Real.sqrt u
  have hs : 0 < σ := Real.sqrt_pos.mpr (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hu))
  have hl : HasLaw (fun z : ℝ => σ*z) (gaussianReal 0 u) GaussianCore.γ := by
    refine ⟨by fun_prop,?_⟩
    simp [GaussianCore.γ,σ,gaussianReal_map_const_mul,Real.sq_sqrt u.coe_nonneg]
  have hf : AEStronglyMeasurable (fun x : ℝ => x • curve g a (b+x))
      (gaussianReal 0 u) :=
    (continuous_id.smul ((curve_continuous g a).comp
      (continuous_const.add continuous_id))).aestronglyMeasurable
  have he := GaussianBoundedHeatDerivative.centered_integral (curve g a)
    (curve_continuous g a) (SchwartzMap.seminorm ℝ 0 0 g) (by positivity)
    (curve_bound g a) b σ
  have hσ : (u : ℝ)*σ⁻¹ = σ := by
    have heq : σ*σ = (u : ℝ) := by
      simpa only [σ,pow_two] using Real.sq_sqrt u.coe_nonneg
    calc
      _ = (σ*σ)*σ⁻¹ := by rw [heq]
      _ = σ := by rw [mul_assoc,mul_inv_cancel₀ (ne_of_gt hs),mul_one]
  calc
    _ = ∫ z : ℝ, (σ*z) • curve g a (b+σ*z) ∂GaussianCore.γ := (hl.integral_comp hf).symm
    _ = σ • ∫ z : ℝ, z • curve g a (b+σ*z) ∂GaussianCore.γ := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (σ*z) • curve g a (b+σ*z) = σ • z • curve g a (b+σ*z)
        rw [smul_smul]
    _ = _ := by
      unfold heatScore GaussianHalfHolderScore.score
      rw [he,smul_smul,hσ]

theorem conditional_endpoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (S T : ℝ≥0)
    (hST : S ≤ T) :
    gaussianProduct[fun Y => (process T Y-process S Y) • curve g a (process T Y) |
      naturalFiltration S] =ᵐ[gaussianProduct] fun Y =>
        ((T-S : ℝ≥0) : ℝ) • heatScore g a (process S Y) (T-S) := by
  let F : (Iic S → ℝ) × ℝ → GaussianL2 :=
    fun p => p.2 • curve g a (p.1 ⟨S,by simp⟩+p.2)
  have hm : Measurable (fun p : (Iic S → ℝ) × ℝ => p.1 ⟨S,by simp⟩+p.2) :=
    ((measurable_pi_apply (⟨S,by simp⟩ : Iic S)).comp measurable_fst).add measurable_snd
  have hf : StronglyMeasurable F := by
    simpa only [F,Function.comp_def,Pi.smul_def'] using measurable_snd.stronglyMeasurable.smul
      ((curve_continuous g a).stronglyMeasurable.comp_measurable hm)
  have hi : Integrable (fun Y => (process T Y-process S Y) • curve g a (process T Y))
      gaussianProduct := bounded_weight_integrable _ _
    ((increment_memLp S T).integrable (by norm_num))
    (((curve_continuous g a).stronglyMeasurable.comp_measurable
      (process_stronglyMeasurable T).measurable).aestronglyMeasurable)
    (SchwartzMap.seminorm ℝ 0 0 g) (fun Y => curve_bound g a _)
  have he : (fun Y => F (past S Y,process T Y-process S Y)) =
      fun Y => (process T Y-process S Y) • curve g a (process T Y) := by
    funext Y
    simp only [F,past,GaussianPredictableStep.pastProcess,add_sub_cancel]
  have h := IndependentInnovationConditioning.conditional_integral gaussianProduct
    (past S) (fun Y => process T Y-process S Y) (past_measurable S)
    ((process_stronglyMeasurable T).measurable.sub (process_stronglyMeasurable S).measurable)
    (past_increment_independent S T hST) F hf (he.symm ▸ hi)
  rw [he,← history_eq_comap S,(increment_law S T hST).map_eq] at h
  filter_upwards [h] with Y hY
  apply hY.trans
  simpa only [F,past,GaussianPredictableStep.pastProcess,NNReal.coe_sub hST] using
    curve_increment g a (process S Y) (T-S)

theorem weighted_endpoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (S T : ℝ≥0)
    (hST : S ≤ T) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ Y, (V Y*(process T Y-process S Y)) • curve g a (process T Y)
      ∂gaussianProduct) =
      ((T-S : ℝ≥0) : ℝ) • ∫ Y, V Y • heatScore g a (process S Y) (T-S)
        ∂gaussianProduct := by
  have hf : AEStronglyMeasurable (fun Y => curve g a (process T Y)) gaussianProduct :=
    ((curve_continuous g a).stronglyMeasurable.comp_measurable
      (process_stronglyMeasurable T).measurable).aestronglyMeasurable
  have hp : Integrable (fun Y => V Y*(process T Y-process S Y)) gaussianProduct :=
    (Lp.memLp V).integrable_mul (increment_memLp S T)
  have hi : Integrable (fun Y => V Y • ((process T Y-process S Y) • curve g a (process T Y)))
      gaussianProduct := by
    simpa only [smul_smul] using bounded_weight_integrable _ _ hp hf
      (SchwartzMap.seminorm ℝ 0 0 g) (fun Y => curve_bound g a _)
  have hj := bounded_weight_integrable _ _ ((increment_memLp S T).integrable (by norm_num))
    hf (SchwartzMap.seminorm ℝ 0 0 g) (fun Y => curve_bound g a _)
  have hc := condExp_smul_of_aestronglyMeasurable_left hV hi hj
  have he := conditional_endpoint g a S T hST
  calc
    _ = ∫ Y, gaussianProduct[fun Y => V Y • ((process T Y-process S Y) • curve g a (process T Y)) |
        naturalFiltration S] Y ∂gaussianProduct := by
      rw [integral_condExp (naturalFiltration.le S)]
      simp only [smul_smul]
    _ = ∫ Y, V Y • (((T-S : ℝ≥0) : ℝ) • heatScore g a (process S Y) (T-S))
        ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [hc,he] with Y hcY heY
      exact hcY.trans (congrArg (fun w : GaussianL2 => V Y • w) heY)
    _ = _ := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun Y => smul_comm _ _ _

theorem terminal_step_closed (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R T : ℝ≥0)
    (hSR : S ≤ R) (hRT : R ≤ T) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ Y, (V Y*(process R Y-process S Y)) • curve g a (process T Y)
      ∂gaussianProduct) =
      ((R-S : ℝ≥0) : ℝ) • ∫ Y, V Y • heatScore g a (process S Y) (T-S)
        ∂gaussianProduct := by
  rcases hRT.eq_or_lt with rfl|hRT
  · exact weighted_endpoint g a S R hSR V hV
  · exact terminal_step g a S R T hSR hRT V hV

theorem weighted_score (g : SchwartzMap ℝ ℝ) (a : ℝ) (S R v : ℝ≥0)
    (hSR : S ≤ R) (hv : 0 < v) (V : GaussianL2)
    (hV : AEStronglyMeasurable[naturalFiltration S] V gaussianProduct) :
    (∫ Y, V Y • heatScore g a (process R Y) v ∂gaussianProduct) =
      ∫ Y, V Y • heatScore g a (process S Y) (((R-S)+v : ℝ≥0) : ℝ) ∂gaussianProduct := by
  have hf : AEStronglyMeasurable (fun Y => heatScore g a (process R Y) v) gaussianProduct :=
    ((heatScore_stronglyMeasurable g a).comp_measurable
      ((process_stronglyMeasurable R).measurable.prodMk measurable_const)).aestronglyMeasurable
  let M : ℝ := (constant g*GaussianHalfHolderScore.mass)/Real.sqrt (Real.sqrt v)
  have hi : Integrable (fun Y => V Y • heatScore g a (process R Y) v) gaussianProduct :=
    bounded_weight_integrable _ _ ((Lp.memLp V).integrable (by norm_num)) hf M
      (fun Y => heatScore_norm g a _ _ hv)
  have hj : Integrable (fun Y => heatScore g a (process R Y) v) gaussianProduct :=
    (integrable_const M).mono' hf
      (Filter.Eventually.of_forall fun Y => heatScore_norm g a _ _ hv)
  have hc := condExp_smul_of_aestronglyMeasurable_left hV hi hj
  have he := conditional_score g a S R v hSR hv
  calc
    _ = ∫ Y, gaussianProduct[fun Y => V Y • heatScore g a (process R Y) v |
        naturalFiltration S] Y ∂gaussianProduct := (integral_condExp (naturalFiltration.le S)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hc,he] with Y hcY heY
      exact hcY.trans (congrArg (fun w : GaussianL2 => V Y • w) heY)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzConditionalIncrement
