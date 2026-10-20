import Foundation.SubquadraticFiniteZeroFactorization
import Foundation.RiemannRealOrderCubicEndpoint
import Foundation.RealRootedVerticalLimit

/-! Actual complex-zero infinitude and the cubic real-order obstruction.
No conclusion about orders approaching one is inferred from a fixed order. -/
noncomputable section
open MeasureTheory Set Filter Complex Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderComplexZeros
open RiemannRealOrderFlow
open RiemannQuarticFlow (halfLine)

theorem actual_subquadratic_growth (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖flow a t z‖ ≤ C*Real.exp (‖z‖*Real.sqrt ‖z‖) := by
  obtain ⟨N,hN⟩ := exists_nat_ge a
  let T := max t 0
  let I := ∫ u : ℝ, RiemannEvenDomain.weighted (N+2) 0 (T+1) 0 u ∂halfLine
  have hI : 0 ≤ I := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact RiemannEvenFlow.weighted_nonneg (N+2) 0 (T+1) 0 u hu
  have hjet (z : ℂ) : ‖jet a 0 t z‖ ≤ Real.exp (T+1+‖z‖*Real.sqrt ‖z‖)*I := by
    have hmajor : Integrable (fun u : ℝ => Real.exp (T+1+‖z‖*Real.sqrt ‖z‖)*
        RiemannEvenDomain.weighted (N+2) 0 (T+1) 0 u) halfLine :=
      (RiemannEvenDomain.weighted_integrable (N+2) 0 (T+1) 0).const_mul _
    have hb : ∀ᵐ u : ℝ ∂halfLine, ‖integrand a 0 t z u‖ ≤
        Real.exp (T+1+‖z‖*Real.sqrt ‖z‖)*RiemannEvenDomain.weighted (N+2) 0 (T+1) 0 u := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      exact (integrand_bound a 0 t z u hu).trans
        (weighted_tilt_bound a N 0 ha hN t T ‖z‖ u (le_max_right _ _) (le_max_left _ _)
          (norm_nonneg z) hu)
    have h := norm_integral_le_of_norm_le hmajor hb
    rw [integral_const_mul] at h
    exact h
  refine ⟨Real.exp (T+1)*(I+1),by positivity,fun z => ?_⟩
  have hp := hjet z
  have hn := hjet (-z)
  rw [norm_neg] at hn
  unfold flow
  rw [norm_div,Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  rw [Real.exp_add] at hp hn
  nlinarith [norm_add_le (jet a 0 t z) (jet a 0 t (-z)),
    Real.exp_pos (T+1),Real.exp_pos (‖z‖*Real.sqrt ‖z‖)]

theorem actual_complex_zero_set_infinite (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    {z : ℂ | flow a t z = 0}.Infinite := by
  have h0 : flow a t 0 ≠ 0 := by
    intro h
    have hp := actual_flow_zero_pos a ha t
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  obtain ⟨C,hC,hgrowth⟩ := actual_subquadratic_growth a ha t
  exact SubquadraticFiniteZeroFactorization.infinite_zeros_of_subquadratic_real_decay
    (flow a t) (flow_differentiable a ha t) h0 C hC hgrowth
    (RiemannRealOrderFourierDecay.flow_real_genuine_and_decay a ha t).2

theorem three_halves_nonreal_zero_set_infinite (t : ℝ) (ht : t ≠ 0) :
    {z : ℂ | flow (3/2) t z = 0 ∧ z.im ≠ 0}.Infinite := by
  have hz := actual_complex_zero_set_infinite (3/2) (by norm_num) t
  have hr := (RiemannRealOrderCubicEndpoint.actual_real_zero_set_finite t ht).image Complex.ofReal
  apply (hz.diff hr).mono
  rintro z ⟨hzero,hnot⟩
  refine ⟨hzero,?_⟩
  intro him
  have hcoe : (z.re : ℂ) = z := by apply Complex.ext <;> simp [him]
  apply hnot
  refine ⟨z.re,?_,hcoe⟩
  change flow (3/2) t (z.re : ℂ) = 0
  change flow (3/2) t z = 0 at hzero
  rw [hcoe]
  exact hzero

theorem no_three_halves_eventual_real_zeros :
    ¬ ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ z : ℂ, flow (3/2) t z = 0 → z.im = 0 := by
  rintro ⟨T,hT⟩
  let t := max T 1
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨z,hz,hi⟩ := (three_halves_nonreal_zero_set_infinite t ht.ne').nonempty
  exact hi (hT t (le_max_left _ _) z hz)

theorem three_halves_no_split_polynomial_limit (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
      TendstoLocallyUniformlyOn
        (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow (3/2) t) atTop univ := by
  rintro ⟨P,hP,hlim⟩
  have h0 : flow (3/2) t 0 ≠ 0 := by
    intro h
    have hp := actual_flow_zero_pos (3/2) (by norm_num) t
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hr := RealRootedVerticalLimit.real_zeros_of_locally_uniform_split_polynomials
    P (flow (3/2) t) (flow_differentiable (3/2) (by norm_num) t) ⟨0,h0⟩ hP hlim
  obtain ⟨z,hz,hi⟩ := (three_halves_nonreal_zero_set_infinite t ht).nonempty
  exact hi (hr z hz)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderComplexZeros
