import Foundation.CauchyPoissonForwardEntropy
/-! Explicit reset minorization and a nonsharp infinitesimal entropy bound for
the zero-drift actual circle Poisson semigroup. No sharp LSI or nonzero-drift
rate is asserted. -/
open Complex MeasureTheory ProbabilityTheory Filter Set InformationTheory
open scoped Topology
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CauchyPoissonQuantitativeEntropy
open CauchyPoissonFlow CauchyPoissonKernelComposition CauchyPoissonMarkovKernel
open CauchyPoissonMixtureEntropy CauchyPoissonForwardEntropy CauchyPoissonDensitySmooth

theorem poisson_lower (v : ℂ) (hv : ‖v‖ < 1) (w : ℂ) (hw : ‖w‖ = 1) :
    (1-‖v‖^2)/4 ≤ poissonKernel 0 v w := by
  have hd : 0 < ‖w-v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (by intro h; rw [← h,hw] at hv; linarith))
  have hb : ‖w-v‖ ≤ 2 := (norm_sub_le w v).trans (by linarith)
  have hn : 0 ≤ 1-‖v‖^2 := by nlinarith [norm_nonneg v]
  simp only [poissonKernel,sub_zero,hw,one_pow]
  apply (le_div_iff₀ (sq_pos_of_pos hd)).mpr
  have hb2 : ‖w-v‖^2 ≤ 4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hb2 hn
  nlinarith [hm]

def reset (t : ℝ) : ℝ := (1-Real.exp (-t)^2)/4

theorem reset_range (t : ℝ) (ht : 0 < t) : 0 < reset t ∧ reset t < 1 := by
  have hp := Real.exp_pos (-t)
  have hlt : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  unfold reset
  constructor <;> nlinarith [sq_nonneg (Real.exp (-t))]

theorem zero_evolution (t : ℝ) (z : ℂ) : evolution 0 t z = (Real.exp (-t):ℂ)*z := by
  simp [evolution,decay,rate,flow,numerator,denominator]

theorem reset_minorization (t : ℝ) (ht : 0 < t) (z : Circle) (θ : ℝ) :
    reset t * poleWeight 0 θ ≤ poleWeight (evolution 0 t z) θ := by
  have hn : ‖evolution 0 t z‖ = Real.exp (-t) := by
    rw [zero_evolution,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; simp
  have hh := poisson_lower (evolution 0 t z)
    (evolution_strict_disk 0 t (by norm_num) ht z (by simp)) (circleMap 0 1 θ) (by simp)
  rw [hn] at hh
  have hw : poissonKernel 0 0 (circleMap 0 1 θ) = 1 := by simp [poissonKernel]
  unfold poleWeight
  rw [hw,mul_one]
  calc
    _ = (2*Real.pi)⁻¹ * ((1-Real.exp (-t)^2)/4) := by unfold reset; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by positivity)

theorem zero_entropy_contraction (t : ℝ) (ht : 0 < t) (μ : Measure Circle)
    [IsProbabilityMeasure μ] :
    klDiv ((kernel 0 t) ∘ₘ μ) (invariantLaw 0) ≤
      ENNReal.ofReal (1-reset t)*klDiv μ (invariantLaw 0) :=
  entropy_contraction 0 t (reset t) (by norm_num) ht (reset_range t ht).1.le
    (reset_range t ht).2 (fun z θ _ => reset_minorization t ht z θ) μ


theorem reset_derivative : HasDerivAt reset (1/2) 0 := by
  change HasDerivAt (fun x : ℝ => (1-Real.exp (-x)^2)/4) (1/2) 0
  convert (((hasDerivAt_neg (0:ℝ)).exp.pow 2).const_sub 1).div_const 4 using 1 <;>
    norm_num [reset]

theorem zero_entropy_production_bound (t : ℝ) (ht : 0 < t) (μ : Measure Circle)
    [IsProbabilityMeasure μ] :
    (∫ w, Real.log (densityCurve 0 (by norm_num) μ t w).re *
      (deriv (densityCurve 0 (by norm_num) μ) t w).re ∂invariantLaw 0) ≤
      -(1/2)*(klDiv ((kernel 0 t) ∘ₘ μ) (invariantLaw 0)).toReal := by
  let E := (klDiv ((kernel 0 t) ∘ₘ μ) (invariantLaw 0)).toReal
  have hd := (actual_kl_derivative 0 t (by norm_num) ht μ).tendsto_slope_zero_right
  have hr := reset_derivative.tendsto_slope_zero_right
  have hr' : Tendsto (fun h : ℝ => -(h⁻¹*reset h)*E) (𝓝[Ioi 0] 0) (𝓝 (-(1/2)*E)) := by
    simpa [reset] using hr.neg.mul_const E
  apply le_of_tendsto_of_tendsto hd hr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  change 0 < h at hh
  let := kernel_markov 0 t (by norm_num) ht.le
  have hc := zero_entropy_contraction h hh ((kernel 0 t) ∘ₘ μ)
  rw [Measure.comp_assoc,kernel_composition 0 t h (by norm_num) ht.le hh.le] at hc
  have hf := CauchyPoissonRegularization.positive_time_entropy_finite 0 t (by norm_num) ht μ
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf) hc
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by linarith [(reset_range h hh).2])] at hreal
  change h⁻¹ * (_-E) ≤ -(h⁻¹*reset h)*E
  have hi := inv_nonneg.mpr hh.le
  have hm := mul_le_mul_of_nonneg_left hreal hi
  dsimp [E] at *
  nlinarith [hm]

end OperatorDerivativeRewrite.Foundation.CauchyPoissonQuantitativeEntropy

