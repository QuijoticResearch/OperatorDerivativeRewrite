import Foundation.GaussianDisplacementContinuity

/-! Nonzero actual Gaussian unitary displacement admits no bounded physical L4 realization. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianDisplacementQuarticObstruction
open GaussianCore GaussianL2QuarticEmbeddingObstruction GaussianDisplacementContinuity
open GaussianDisplacementFromPoisson PoissonTiltSourceGauge PoissonTiltHellingerGeometry
private instance : Fact ((1 : ℝ≥0∞)≤4) := ⟨by norm_num⟩

def coherentFour (a : ℝ) : Lp ℝ 4 γ := Real.exp (-a^2) • classFour a

theorem coherentFour_coeFn (a : ℝ) : coherentFour a =ᵐ[γ] fun x => Real.exp (a*x-a^2) := by
  filter_upwards [Lp.coeFn_smul (Real.exp (-a^2)) (classFour a),(exponential_memLp_four a).coeFn_toLp] with x hs hf
  change (Real.exp (-a^2) • classFour a) x=_
  change classFour a x=Real.exp (a*x) at hf
  rw [hs,Pi.smul_apply,hf,smul_eq_mul,← Real.exp_add]
  congr 1
  ring

theorem coherentTwo_coeFn (a : ℝ) : gaussianRoot a =ᵐ[γ] fun x => Real.exp (a*x-a^2) := by
  filter_upwards [Lp.coeFn_smul (Real.exp (-a^2)) (classTwo a),(gaussian_exp_memLp_two a).coeFn_toLp] with x hs hf
  change (Real.exp (-a^2) • classTwo a) x=_
  change classTwo a x=Real.exp (a*x) at hf
  rw [hs,Pi.smul_apply,hf,smul_eq_mul,← Real.exp_add]
  congr 1
  ring

theorem coherentFour_norm (a : ℝ) : ‖coherentFour a‖=Real.exp (a^2) := by
  rw [coherentFour,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),classFour_norm,← Real.exp_add]
  congr 1
  ring

theorem displaced_coherent_physical (rate : ℝ≥0) (hr : 0<rate) (θ a : ℝ) :
    gaussianDisplacement rate hr θ (gaussianRoot a) =ᵐ[γ]
      fun x => Real.exp ((displacement rate θ+a)*x-(displacement rate θ+a)^2) := by
  rw [displacement_coherent]
  exact coherentTwo_coeFn _

theorem no_uniform_quartic_displacement_bound (d : ℝ) (hd : d≠0) (K : ℝ) :
    ∃ a : ℝ, K*‖coherentFour a‖<‖coherentFour (d+a)‖ := by
  let a := (|K|+1)/(2*d)
  have hden : (2 : ℝ)*d≠0 := mul_ne_zero (by norm_num) hd
  have ha : 2*d*a=|K|+1 := by dsimp [a]; field_simp
  refine ⟨a, ?_⟩
  rw [coherentFour_norm,coherentFour_norm]
  have he : K<Real.exp (2*d*a+d^2) := by
    have hh := Real.add_one_le_exp (2*d*a+d^2)
    nlinarith [le_abs_self K,sq_nonneg d]
  have hm := mul_lt_mul_of_pos_right he (Real.exp_pos (a^2))
  rw [← Real.exp_add] at hm
  have heq : 2*d*a+d^2+a^2=(d+a)^2 := by ring
  rwa [heq] at hm

theorem no_bounded_quartic_realization (rate : ℝ≥0) (hr : 0<rate) (θ : ℝ)
    (hd : displacement rate θ≠0) (T : Lp ℝ 4 γ →L[ℝ] Lp ℝ 4 γ) :
    ¬ (∀ a : ℝ, T (coherentFour a)=coherentFour (displacement rate θ+a)) := by
  intro hT
  obtain ⟨a,ha⟩ := no_uniform_quartic_displacement_bound (displacement rate θ) hd ‖T‖
  have hb := T.le_opNorm (coherentFour a)
  rw [hT a] at hb
  exact (not_le_of_gt ha) hb

end OperatorDerivativeRewrite.Foundation.GaussianDisplacementQuarticObstruction
