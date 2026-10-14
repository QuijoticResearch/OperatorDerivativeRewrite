import Foundation.GaussianDensity
import Foundation.BanachLpDualityFour
import Foundation.BochnerL2Dominated

/-! The physical scalar Gaussian L2-to-L4 inclusion has no bounded extension,
even when tested only on actual exponential functions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianL2QuarticEmbeddingObstruction
open GaussianCore BanachLpDualityFour
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem exponential_memLp_four (θ : ℝ) : MemLp (fun x : ℝ => Real.exp (θ*x)) 4 γ := by
  rw [← integrable_norm_rpow_iff (by fun_prop) (by simp) (by simp)]
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (4*θ) using 1
  funext x
  simp only [ENNReal.toReal_ofNat,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [show Real.exp (θ*x)^(4 : ℝ)=Real.exp (θ*x)^(4 : ℕ) from Real.rpow_natCast _ 4]
  rw [← Real.exp_nat_mul]
  congr 1
  ring

def classTwo (θ : ℝ) : GaussianL2 := (gaussian_exp_memLp_two θ).toLp (fun x => Real.exp (θ*x))
def classFour (θ : ℝ) : Lp ℝ 4 γ := (exponential_memLp_four θ).toLp (fun x => Real.exp (θ*x))

theorem exponential_integral (θ : ℝ) : (∫ x, Real.exp (θ*x) ∂γ)=Real.exp (θ^2/2) := by
  have he := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) θ
  simpa [mgf,γ] using he

theorem classTwo_norm (θ : ℝ) : ‖classTwo θ‖=Real.exp (θ^2) := by
  have he : ‖classTwo θ‖^2=Real.exp (2*θ^2) := by
    rw [BochnerL2Dominated.norm_sq_integral]
    calc
      _ = ∫ x, Real.exp ((2*θ)*x) ∂γ := by
        apply integral_congr_ae
        filter_upwards [(gaussian_exp_memLp_two θ).coeFn_toLp] with x hx
        change classTwo θ x=Real.exp (θ*x) at hx
        rw [hx]
        simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ = _ := by rw [exponential_integral]; congr 1; ring
  have hp : (Real.exp (θ^2))^2=Real.exp (2*θ^2) := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [norm_nonneg (classTwo θ),Real.exp_pos (θ^2)]

theorem classFour_norm (θ : ℝ) : ‖classFour θ‖=Real.exp (2*θ^2) := by
  have he : ‖classFour θ‖^4=Real.exp (8*θ^2) := by
    rw [← quartic_integral_eq_norm]
    calc
      _ = ∫ x, Real.exp ((4*θ)*x) ∂γ := by
        apply integral_congr_ae
        filter_upwards [(exponential_memLp_four θ).coeFn_toLp] with x hx
        change classFour θ x=Real.exp (θ*x) at hx
        rw [hx,← Real.exp_nat_mul]
        congr 1
        ring
      _ = _ := by rw [exponential_integral]; congr 1; ring
  apply (pow_left_inj₀ (norm_nonneg _) (Real.exp_pos _).le (by decide : (4 : ℕ)≠0)).mp
  rw [he,← Real.exp_nat_mul]
  congr 1
  ring

theorem no_uniform_norm_bound (K : ℝ) : ∃ θ : ℝ, K*‖classTwo θ‖ < ‖classFour θ‖ := by
  refine ⟨|K|+1, ?_⟩
  rw [classTwo_norm,classFour_norm]
  have he : K<Real.exp ((|K|+1)^2) := by
    have hh := Real.add_one_le_exp ((|K|+1)^2)
    nlinarith [abs_nonneg K,le_abs_self K]
  have hm := mul_lt_mul_of_pos_right he (Real.exp_pos ((|K|+1)^2))
  have hp : Real.exp ((|K|+1)^2)*Real.exp ((|K|+1)^2)=Real.exp (2*(|K|+1)^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [hp] at hm

theorem no_bounded_physical_extension (T : GaussianL2 →L[ℝ] Lp ℝ 4 γ) :
    ¬ (∀ θ : ℝ, T (classTwo θ)=classFour θ) := by
  intro hT
  obtain ⟨θ,hθ⟩ := no_uniform_norm_bound ‖T‖
  have hb := T.le_opNorm (classTwo θ)
  rw [hT θ] at hb
  exact (not_le_of_gt hθ) hb

end OperatorDerivativeRewrite.Foundation.GaussianL2QuarticEmbeddingObstruction
