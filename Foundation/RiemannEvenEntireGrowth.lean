import Foundation.RiemannQuarticEntireGrowth
import Foundation.RiemannSixthTransitionSimpleZeros
/-! Subquadratic bounds for the actual integer-even hierarchy and all its jets.
For a fixed finite order range and an upper time bound, one constant works
simultaneously for every order, time and complex frequency in the theorem. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenEntireGrowth
open RiemannEvenDomain RiemannEvenFlow RiemannQuarticKernel
open RiemannQuarticFlow (halfLine)

private theorem power_absorbed (a b : ℕ) (hab : a ≤ b) (u : ℝ) (hu : 0 ≤ u) :
    u^a ≤ 1+u^b := by
  by_cases h : u ≤ 1
  · have hh := pow_le_pow_left₀ hu h a
    simp only [one_pow] at hh
    linarith [pow_nonneg hu b]
  · have hh := pow_le_pow_right₀ (le_of_not_ge h) hab
    linarith

theorem weighted_tilt_bound (N m k : ℕ) (hm : m ≤ N) (t T R u : ℝ)
    (hT : 0 ≤ T) (ht : t ≤ T) (hR : 0 ≤ R) (hu : 0 ≤ u) :
    weighted m k t R u ≤ Real.exp (T+1+R*Real.sqrt R)*weighted (N+2) k (T+1) 0 u := by
  have hp := power_absorbed (2*m) (2*(N+2)) (by omega) u hu
  have h3 := power_absorbed 3 (2*(N+2)) (by omega) u hu
  have hlin := RiemannQuarticEntireGrowth.linear_tilt_bound R u hR hu
  have htime := mul_le_mul_of_nonneg_right ht (pow_nonneg hu (2*m))
  have hpoly := mul_le_mul_of_nonneg_left hp hT
  have hphase : t*u^(2*m)+R*u ≤ T+1+R*Real.sqrt R+(T+1)*u^(2*(N+2)) := by
    nlinarith
  have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hphase) (pow_nonneg hu k)
  have hbound := mul_le_mul_of_nonneg_right he (kernel_pos u hu).le
  convert hbound using 1 <;>
    simp only [weighted,zero_mul,add_zero,Real.exp_add] <;> ring

theorem jet_growth_bound (N m k : ℕ) (hm : m ≤ N) (t T : ℝ)
    (hT : 0 ≤ T) (ht : t ≤ T) (z : ℂ) :
    ‖jet m k t z‖ ≤ Real.exp (T+1+‖z‖*Real.sqrt ‖z‖)*
      (∫ u : ℝ, weighted (N+2) k (T+1) 0 u ∂halfLine) := by
  have hmajor : Integrable (fun u : ℝ =>
      Real.exp (T+1+‖z‖*Real.sqrt ‖z‖)*weighted (N+2) k (T+1) 0 u) halfLine :=
    (weighted_integrable (N+2) k (T+1) 0).const_mul _
  have hpoint : ∀ᵐ u : ℝ ∂halfLine,
      ‖integrand m k t z u‖ ≤
        Real.exp (T+1+‖z‖*Real.sqrt ‖z‖)*weighted (N+2) k (T+1) 0 u := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact (integrand_bound m k t z u hu).trans
      (weighted_tilt_bound N m k hm t T ‖z‖ u hT ht (norm_nonneg z) hu)
  have h := norm_integral_le_of_norm_le hmajor hpoint
  rw [integral_const_mul] at h
  exact h

theorem exists_uniform_jet_growth (N k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≤ N → ∀ t : ℝ, t ≤ T → ∀ z : ℂ,
      ‖jet m k t z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
  let I := ∫ u : ℝ, weighted (N+2) k (T+1) 0 u ∂halfLine
  have hI : 0 ≤ I := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact weighted_nonneg (N+2) k (T+1) 0 u hu
  refine ⟨Real.exp (T+1)*(I+1),by positivity,?_⟩
  intro m hm t ht z
  apply (jet_growth_bound N m k hm t T hT ht z).trans
  rw [Real.exp_add]
  change Real.exp (T+1)*Real.exp (‖z‖*Real.sqrt ‖z‖)*I ≤ _
  nlinarith [Real.exp_pos (T+1),Real.exp_pos (‖z‖*Real.sqrt ‖z‖)]

theorem exists_uniform_flow_growth (N : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≤ N → ∀ t : ℝ, t ≤ T → ∀ z : ℂ,
      ‖flow m t z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_jet_growth N 0 T hT
  refine ⟨C,hC,?_⟩
  intro m hm t ht z
  have hp := h m hm t ht z
  have hn := h m hm t ht (-z)
  rw [norm_neg] at hn
  unfold flow
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [norm_add_le (jet m 0 t z) (jet m 0 t (-z))]

theorem exists_subquadratic_growth (m : ℕ) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow m t z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_flow_growth m (max t 0) (le_max_right _ _)
  exact ⟨C,hC,h m le_rfl t (le_max_left _ _)⟩

theorem exists_uniform_spatial_derivative_growth (N k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, m ≤ N → ∀ t : ℝ, t ≤ T → ∀ z : ℂ,
      ‖iteratedDeriv k (flow m t) z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
  obtain ⟨C,hC,h⟩ := exists_uniform_jet_growth N k T hT
  refine ⟨C,hC,?_⟩
  intro m hm t ht z
  have hp := h m hm t ht z
  have hn := h m hm t ht (-z)
  rw [norm_neg] at hn
  rw [RiemannEvenEvolution.flow_iteratedDeriv,RiemannEvenEvolution.symmetricJet]
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have htri := norm_add_le (jet m k t z) ((-1 : ℂ)^k*jet m k t (-z))
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul] at htri
  linarith

theorem exists_three_halves_growth (m : ℕ) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow m t z‖ ≤ C*Real.exp (‖z‖^(3/2 : ℝ)) := by
  obtain ⟨C,hC,h⟩ := exists_subquadratic_growth m t
  refine ⟨C,hC,?_⟩
  intro z
  have he : ‖z‖*Real.sqrt ‖z‖=‖z‖^(3/2 : ℝ) := by
    by_cases hz : ‖z‖=0
    · simp [hz]
    · have hp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
      calc
        _ = ‖z‖^(1 : ℝ)*‖z‖^(1/2 : ℝ) := by rw [Real.rpow_one,Real.sqrt_eq_rpow]
        _ = ‖z‖^((1 : ℝ)+1/2) := (Real.rpow_add hp 1 (1/2)).symm
        _ = _ := by norm_num
  simpa only [he] using h z

theorem actual_real_entire_nonzero_subquadratic (m : ℕ) (t : ℝ) :
    Differentiable ℂ (flow m t) ∧ flow m t 0 ≠ 0 ∧
      (∀ x : ℝ, (flow m t (x : ℂ)).im=0) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow m t z‖ ≤ C*Real.exp (‖z‖^(3/2 : ℝ))) := by
  have hp := RiemannEvenNormalizedCompact.actual_flow_zero_pos m t
  refine ⟨flow_differentiable m t,?_,?_,exists_three_halves_growth m t⟩
  · intro hz
    rw [hz,Complex.zero_re] at hp
    linarith
  · intro x
    have hc := RiemannEvenWindowZeros.flow_conj m t (x : ℂ)
    simp only [Complex.conj_ofReal] at hc
    have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    linarith

theorem eventually_sixth_real_entire_nonzero_subquadratic :
    ∀ᶠ t : ℝ in atTop,
      Differentiable ℂ (flow 3 t) ∧ flow 3 t 0 ≠ 0 ∧
      (∀ x : ℝ, (flow 3 t (x : ℂ)).im=0) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow 3 t z‖ ≤ C*Real.exp (‖z‖^(3/2 : ℝ))) ∧
      ∀ z : ℂ, flow 3 t z=0 → z.im=0 ∧ deriv (flow 3 t) z ≠ 0 := by
  filter_upwards [RiemannSixthTransitionSimpleZeros.eventually_all_zeros_real_simple] with t hz
  have h := actual_real_entire_nonzero_subquadratic 3 t
  exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,hz⟩

end OperatorDerivativeRewrite.Foundation.RiemannEvenEntireGrowth
