import Foundation.RiemannQuarticUniformFarScale
/-! Actual subquadratic growth and nontriviality of the quartic arithmetic
flow. These are hypotheses for a classical Laguerre-Polya characterization;
no class-membership or factorization theorem is assumed here. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticEntireGrowth
open RiemannQuarticDomain RiemannQuarticFlow RiemannQuarticKernel

theorem linear_tilt_bound (R u : ℝ) (hR : 0 ≤ R) (hu : 0 ≤ u) :
    R*u ≤ u^3+R*Real.sqrt R := by
  by_cases h : u ≤ Real.sqrt R
  · have hm := mul_le_mul_of_nonneg_left h hR
    nlinarith [pow_nonneg hu 3]
  · have hs : Real.sqrt R ≤ u := (lt_of_not_ge h).le
    have hh := pow_le_pow_left₀ (Real.sqrt_nonneg R) hs 2
    rw [Real.sq_sqrt hR] at hh
    have hm := mul_le_mul_of_nonneg_right hh hu
    nlinarith [Real.sqrt_nonneg R]

theorem cubic_absorbed (u : ℝ) (hu : 0 ≤ u) : u^3 ≤ u^4+1 := by
  by_cases h : u ≤ 1
  · have hp := pow_le_pow_left₀ hu h 3
    norm_num at hp
    nlinarith [pow_nonneg hu 4]
  · have h1 : 1 ≤ u := (lt_of_not_ge h).le
    have hm := mul_le_mul_of_nonneg_right h1 (pow_nonneg hu 3)
    nlinarith

theorem weighted_tilt_bound (t R u : ℝ) (hR : 0 ≤ R) (hu : 0 ≤ u) :
    weighted 0 t R u ≤ Real.exp (1+R*Real.sqrt R)*weighted 0 (t+1) 0 u := by
  have hphase : t*u^4+R*u ≤ (1+R*Real.sqrt R)+(t+1)*u^4 := by
    linarith [linear_tilt_bound R u hR hu,cubic_absorbed u hu]
  have hm := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hphase) (kernel_pos u hu).le
  simpa only [weighted,pow_zero,one_mul,zero_mul,add_zero,Real.exp_add,mul_assoc] using hm

theorem jet_growth_bound (t : ℝ) (z : ℂ) :
    ‖jet 0 t z‖ ≤ Real.exp (1+‖z‖*Real.sqrt ‖z‖)*
      (∫ u : ℝ, weighted 0 (t+1) 0 u ∂halfLine) := by
  have hmajor : Integrable (fun u : ℝ => Real.exp (1+‖z‖*Real.sqrt ‖z‖)*weighted 0 (t+1) 0 u) halfLine :=
    (weighted_integrable 0 (t+1) 0).const_mul _
  have hpoint : ∀ᵐ u : ℝ ∂halfLine,
      ‖integrand 0 t z u‖ ≤ Real.exp (1+‖z‖*Real.sqrt ‖z‖)*weighted 0 (t+1) 0 u := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact (integrand_bound 0 t z u hu).trans (weighted_tilt_bound t ‖z‖ u (norm_nonneg z) hu)
  have h := norm_integral_le_of_norm_le hmajor hpoint
  rw [integral_const_mul] at h
  exact h

theorem flow_growth_bound (t : ℝ) (z : ℂ) :
    ‖flow t z‖ ≤ Real.exp (1+‖z‖*Real.sqrt ‖z‖)*
      (∫ u : ℝ, weighted 0 (t+1) 0 u ∂halfLine) := by
  have hp := jet_growth_bound t z
  have hn := jet_growth_bound t (-z)
  rw [norm_neg] at hn
  unfold flow
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [norm_add_le (jet 0 t z) (jet 0 t (-z))]

theorem exists_subquadratic_growth (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow t z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
  let I := ∫ u : ℝ, weighted 0 (t+1) 0 u ∂halfLine
  have hI : 0 ≤ I := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact weighted_nonneg 0 (t+1) 0 u hu
  refine ⟨Real.exp 1*(I+1),by positivity,?_⟩
  intro z
  apply (flow_growth_bound t z).trans
  rw [Real.exp_add]
  change Real.exp 1*Real.exp (‖z‖*Real.sqrt ‖z‖)*I ≤ _
  nlinarith [Real.exp_pos (‖z‖*Real.sqrt ‖z‖),Real.exp_pos (1 : ℝ)]

theorem exists_three_halves_growth (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow t z‖ ≤ C*Real.exp (‖z‖^(3/2 : ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := exists_subquadratic_growth t
  refine ⟨C,hC,?_⟩
  intro z
  have he : ‖z‖*Real.sqrt ‖z‖=‖z‖^(3/2 : ℝ) := by
    by_cases hz : ‖z‖=0
    · simp [hz]
    · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
      calc
        _ = ‖z‖^(1 : ℝ)*‖z‖^(1/2 : ℝ) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
        _ = ‖z‖^((1 : ℝ)+1/2) := (Real.rpow_add hzpos 1 (1/2)).symm
        _ = _ := by norm_num
  simpa only [he] using hbound z

theorem eventually_real_entire_nonzero_subquadratic :
    ∀ᶠ t : ℝ in atTop,
      Differentiable ℂ (flow t) ∧ flow t 0 ≠ 0 ∧
      (∀ x : ℝ, (flow t (x : ℂ)).im=0) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow t z‖ ≤ C*Real.exp (‖z‖^(3/2 : ℝ))) ∧
      ∀ z : ℂ, flow t z=0 → z.im=0 := by
  filter_upwards [RiemannQuarticUniformFarScale.eventually_all_zeros_real] with t hz
  have hn := RiemannQuarticReality.flow_ne_zero_on_imaginary_axis t 0
  simp only [Complex.ofReal_zero,mul_zero] at hn
  exact ⟨flow_differentiable t,hn,RiemannQuarticReality.flow_im_zero t,
    exists_three_halves_growth t,hz⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticEntireGrowth
