import Foundation.PeriodicSlabGround
import Foundation.YMPositiveMixing

/-! The existing reset estimate rules out bounded centered harmonic functions
for each actual periodic ground transition. No uniform coupling rate is claimed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicGroundHarmonic
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround

variable {beta : ℝ} (g : GroundData beta)

theorem density_bounds : ∃ m M : ℝ,0<m ∧
    ∀ U V : State,m ≤ g.density U V ∧ g.density U V ≤ M := by
  have hu (U : State) : g.function U ≤ g.upper := (le_abs_self _).trans (g.bounds U).2
  have hup : 0 < g.upper := (g.function_pos 1).trans_le (hu 1)
  let m := Real.exp (-768*|beta|)*g.lower/(g.value*g.upper)
  let M := Real.exp (768*|beta|)*g.upper/(g.value*g.lower)
  refine ⟨m,M,div_pos (mul_pos (Real.exp_pos _) g.lower_pos) (mul_pos g.value_pos hup),?_⟩
  intro U V
  have hnum : Real.exp (-768*|beta|)*g.lower ≤ kernel beta U V*g.function V :=
    mul_le_mul (kernel_bounds beta U V).1 (g.bounds V).1 g.lower_pos.le
      (kernel_positive beta U V).le
  have hupper : kernel beta U V*g.function V ≤ Real.exp (768*|beta|)*g.upper :=
    mul_le_mul (kernel_bounds beta U V).2 (hu V) (g.function_pos V).le (Real.exp_pos _).le
  unfold GroundData.density
  constructor
  · calc
      m ≤ (kernel beta U V*g.function V)/(g.value*g.upper) :=
        div_le_div_of_nonneg_right hnum (mul_pos g.value_pos hup).le
      _ ≤ _ := div_le_div_of_nonneg_left
        (mul_pos (kernel_positive beta U V) (g.function_pos V)).le
        (mul_pos g.value_pos (g.function_pos U)) (mul_le_mul_of_nonneg_left (hu U) g.value_pos.le)
  · calc
      _ ≤ (Real.exp (768*|beta|)*g.upper)/(g.value*g.function U) :=
        div_le_div_of_nonneg_right hupper (mul_pos g.value_pos (g.function_pos U)).le
      _ ≤ M := div_le_div_of_nonneg_left (mul_pos (Real.exp_pos _) hup).le
        (mul_pos g.value_pos g.lower_pos) (mul_le_mul_of_nonneg_left (g.bounds U).1 g.value_pos.le)

theorem average_transition (f : State → ℝ) (U : State) :
    YMPositiveKernel.average boundaryHaar g.density f U=∫ V,f V ∂g.transition U := by
  unfold YMPositiveKernel.average YMPositiveKernel.rowDensity YMPositiveKernel.mass
  rw [g.density_integral]
  simp only [div_one]
  rw [g.transition_apply,integral_withDensity_eq_integral_toReal_smul
    ((Measurable.of_uncurry_left g.density_measurable).ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (g.density_pos _ _).le,smul_eq_mul]

theorem centered_harmonic_zero (f : State → ℝ) (hf : Measurable f)
    (hz : (∫ U,f U ∂g.stationary)=0) (B : ℝ) (hb : ∀ U,|f U| ≤ B)
    (hh : ∀ U,YMPositiveKernel.average boundaryHaar g.density f U=f U) (U : State) : f U=0 := by
  letI : IsProbabilityMeasure g.stationary := g.stationary_probability
  obtain ⟨m,M,hm,hk⟩ := density_bounds g
  have hM : 0 < M := (g.density_pos 1 1).trans_le (hk 1 1).2
  have hq0 : 0 ≤ 1-m/M := sub_nonneg.mpr ((div_le_one₀ hM).mpr ((hk 1 1).1.trans (hk 1 1).2))
  have hq1 : 1-m/M < 1 := by have := div_pos hm hM; linarith
  have hn (n : ℕ) : |f U| ≤ 2*B*(1-m/M)^n :=
    YMPositiveMixing.centered_iterate_bound boundaryHaar g.stationary g.density m M
      g.density_measurable hm hk (fun _ => f) (fun _ => hf) (fun _ V => (hh V).symm)
      (fun _ => hz) B hb n U
  have ht : Tendsto (fun n : ℕ => 2*B*(1-m/M)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (2*B)
  exact abs_eq_zero.mp (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hn)) (abs_nonneg _))

end OperatorDerivativeRewrite.Foundation.PeriodicGroundHarmonic
