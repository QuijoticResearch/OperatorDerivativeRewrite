import Foundation.RiemannRealOrderCutoffRate
import Foundation.RiemannRealOrderRelativeObstruction

/-! Quantified real-frequency transition near the quadratic order.
Relative control is restricted by an explicit order-gap factor. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderTransitionRate
open RiemannRealOrderFractionalCoefficient RiemannRealOrderRelativeObstruction
open RiemannRealOrderUniformAsymptotic RiemannRealOrderCutoffRate

theorem actual_absolute_error_uniform_rate (t : ℝ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ a : ℝ, 1 < a → a ≤ 5/4 → ∀ x : ℝ, 1 ≤ x →
      ‖scaledValue a t x-(leading a t : ℂ)‖ ≤ C*x^(-(1/2 : ℝ)) := by
  obtain ⟨R,hR,hr⟩ := scaled_remainder_uniform_bound t
  obtain ⟨Q,hQ,hq⟩ := actual_cutoff_sine_uniform_rate t
  refine ⟨R+Q,by positivity,?_⟩
  intro a ha ha5 x hx
  have hx0 : 0 < x := by linarith
  have hinv : x⁻¹ ≤ x^(-(1/2 : ℝ)) := by
    simpa only [Real.rpow_neg_one] using
      Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (-1 : ℝ) ≤ -(1/2 : ℝ))
  rw [scaledValue,actual_scaled_decomposition a t x ha ha5 hx0,add_sub_assoc]
  calc
    _ ≤ ‖((x^(2*a-2) : ℝ) : ℂ)*RiemannRealOrderFractionalFourier.sineRemainder a t x‖+
        ‖((x^(2*a-2) : ℝ) : ℂ)*(∫ u : ℝ in Ioi 0,
          RiemannRealOrderFractionalJets.cutoff a t u*(Real.sin (x*u) : ℂ))-(leading a t : ℂ)‖ :=
      norm_add_le _ _
    _ ≤ R*x^(-(1/2 : ℝ))+Q*x⁻¹ := add_le_add (hr a ha ha5 x hx) (hq a ha ha5 x hx)
    _ ≤ R*x^(-(1/2 : ℝ))+Q*x^(-(1/2 : ℝ)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv hQ)
    _ = _ := by ring

theorem leading_linear_lower_near_one (t : ℝ) (ht : t ≠ 0) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ a : ℝ, 1 < a → a < 1+δ → c*(a-1) ≤ |leading a t| := by
  let d : ℝ := 2*Real.pi*t*RiemannQuarticKernel.kernel 0
  have hd : 0 < |d| := abs_pos.mpr (by
    dsimp [d]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) ht)
      (ne_of_gt (RiemannQuarticKernel.kernel_pos 0 (by norm_num))))
  let c : ℝ := |d|/2
  have hc : 0 < c := by dsimp [c]; positivity
  have hl : Tendsto (fun a : ℝ => |leading a t/(a-1)|) (𝓝[>] 1) (𝓝 |d|) :=
    (leading_div_order_gap_limit t).abs
  have he : ∀ᶠ a : ℝ in 𝓝[>] 1, c < |leading a t/(a-1)| :=
    (tendsto_order.1 hl).1 c (by dsimp [c]; linarith)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhdsWithin_iff.mp he
  refine ⟨δ,c,hδ,hc,?_⟩
  intro a ha haδ
  have hdist : a ∈ Metric.ball (1 : ℝ) δ := by
    rw [Metric.mem_ball,Real.dist_eq,abs_of_pos (sub_pos.mpr ha)]
    linarith
  have h := hball ⟨hdist,ha⟩
  change c < |leading a t/(a-1)| at h
  rw [abs_div,abs_of_pos (sub_pos.mpr ha)] at h
  exact (le_div_iff₀ (sub_pos.mpr ha)).mp h.le

theorem actual_relative_error_bound (t : ℝ) (ht : t ≠ 0) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ 0 ≤ C ∧
      ∀ a : ℝ, 1 < a → a < 1+δ → ∀ x : ℝ, 1 ≤ x →
        ‖scaledValue a t x/(leading a t : ℂ)-1‖ ≤ C*((a-1)⁻¹*x^(-(1/2 : ℝ))) := by
  obtain ⟨A,hA,herror⟩ := actual_absolute_error_uniform_rate t
  obtain ⟨δ,c,hδ,hc,hlower⟩ := leading_linear_lower_near_one t ht
  refine ⟨min δ (1/4),A/c,lt_min hδ (by norm_num),min_le_right _ _,by positivity,?_⟩
  intro a ha haδ x hx
  have had : a < 1+δ := lt_of_lt_of_le haδ (add_le_add le_rfl (min_le_left _ _))
  have ha5 : a ≤ 5/4 := by have h := min_le_right δ (1/4); linarith
  have hL := leading_ne_zero a t ha (by linarith) ht
  have he : scaledValue a t x/(leading a t : ℂ)-1=
      (scaledValue a t x-(leading a t : ℂ))/(leading a t : ℂ) := by
    field_simp [Complex.ofReal_ne_zero.mpr hL]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (A*x^(-(1/2 : ℝ)))/|leading a t| :=
      div_le_div_of_nonneg_right (herror a ha ha5 x hx) (abs_nonneg _)
    _ ≤ (A*x^(-(1/2 : ℝ)))/(c*(a-1)) :=
      div_le_div_of_nonneg_left (mul_nonneg hA (Real.rpow_nonneg (by linarith) _))
        (mul_pos hc (sub_pos.mpr ha)) (hlower a ha had)
    _ = _ := by field_simp [hc.ne',ne_of_gt (sub_pos.mpr ha)]

theorem actual_nonzero_in_transition_region (t : ℝ) (ht : t ≠ 0) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ 0 < K ∧
      ∀ a : ℝ, 1 < a → a < 1+δ → ∀ x : ℝ, 1 ≤ x →
        K < (a-1)*x^(1/2 : ℝ) → RiemannRealOrderFlow.flow a t (x : ℂ)≠0 := by
  obtain ⟨δ,C,hδ,hδ4,hC,hbound⟩ := actual_relative_error_bound t ht
  refine ⟨δ,C+1,hδ,hδ4,by linarith,?_⟩
  intro a ha haδ x hx hscale hzero
  have hx0 : 0 < x := by linarith
  have heq : (a-1)⁻¹*x^(-(1/2 : ℝ))=((a-1)*x^(1/2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hx0.le,mul_inv_rev]
    ring
  have hb := hbound a ha haδ x hx
  rw [heq,← div_eq_mul_inv] at hb
  have hsmall : C/((a-1)*x^(1/2 : ℝ)) < 1 :=
    (div_lt_one (by linarith : 0 < (a-1)*x^(1/2 : ℝ))).mpr (by linarith)
  have h := hb.trans_lt hsmall
  simp only [scaledValue,hzero,mul_zero,zero_div,zero_sub,norm_neg,norm_one] at h
  exact (lt_irrefl (1 : ℝ)) h

theorem actual_relative_diagonal_limit (t : ℝ) (ht : t ≠ 0) (a x : ℕ → ℝ)
    (ha : Tendsto a atTop (𝓝[>] 1)) (hx : Tendsto x atTop atTop)
    (hscale : Tendsto (fun n : ℕ => (a n-1)*x n^(1/2 : ℝ)) atTop atTop) :
    Tendsto (fun n : ℕ => scaledValue (a n) t (x n)/(leading (a n) t : ℂ)) atTop (𝓝 1) := by
  obtain ⟨δ,C,hδ,hδ4,hC,hbound⟩ := actual_relative_error_bound t ht
  have hr : Tendsto (fun n : ℕ => C*((a n-1)*x n^(1/2 : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using (tendsto_inv_atTop_zero.comp hscale).const_mul C
  have habove : ∀ᶠ n : ℕ in atTop, 1 < a n := ha.eventually self_mem_nhdsWithin
  have hnb : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), r < 1+δ :=
    Iio_mem_nhds (by linarith : (1 : ℝ) < 1+δ)
  have hbelow : ∀ᶠ n : ℕ in atTop, a n < 1+δ :=
    ha.eventually (hnb.filter_mono nhdsWithin_le_nhds)
  have he : Tendsto (fun n : ℕ =>
      scaledValue (a n) t (x n)/(leading (a n) t : ℂ)-1) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hr
    filter_upwards [habove,hbelow,hx.eventually_ge_atTop 1] with n han had hxn
    have h := hbound (a n) han had (x n) hxn
    have hx0 : 0 < x n := by linarith
    have heq : (a n-1)⁻¹*x n^(-(1/2 : ℝ))=((a n-1)*x n^(1/2 : ℝ))⁻¹ := by
      rw [Real.rpow_neg hx0.le,mul_inv_rev]
      ring
    simpa only [heq] using h
  simpa only [sub_add_cancel,zero_add] using he.add_const 1

theorem actual_nonzero_two_sided_region (t : ℝ) (ht : t ≠ 0) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ 0 < K ∧
      ∀ a : ℝ, 1 < a → a < 1+δ → ∀ x : ℝ, 1 ≤ |x| →
        K < (a-1)*|x|^(1/2 : ℝ) → RiemannRealOrderFlow.flow a t (x : ℂ)≠0 := by
  obtain ⟨δ,K,hδ,hδ4,hK,hbound⟩ := actual_nonzero_in_transition_region t ht
  refine ⟨δ,K,hδ,hδ4,hK,?_⟩
  intro a ha haδ x hx hscale
  rcases le_or_gt 0 x with hx0 | hx0
  · rw [abs_of_nonneg hx0] at hx hscale
    exact hbound a ha haδ x hx hscale
  · rw [abs_of_neg hx0] at hx hscale
    have h := hbound a ha haδ (-x) hx hscale
    simpa only [Complex.ofReal_neg,RiemannRealOrderFlow.flow_even] using h

theorem real_zero_transition_bound (t : ℝ) (ht : t ≠ 0) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ 0 < K ∧
      ∀ a : ℝ, 1 < a → a < 1+δ → ∀ x : ℝ, 1 ≤ |x| →
        RiemannRealOrderFlow.flow a t (x : ℂ)=0 → (a-1)*|x|^(1/2 : ℝ) ≤ K := by
  obtain ⟨δ,K,hδ,hδ4,hK,hbound⟩ := actual_nonzero_two_sided_region t ht
  refine ⟨δ,K,hδ,hδ4,hK,?_⟩
  intro a ha haδ x hx hz
  by_contra h
  exact hbound a ha haδ x hx (lt_of_not_ge h) hz

theorem real_zero_radius_bound (t : ℝ) (ht : t ≠ 0) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1/4 ∧ 0 < K ∧
      ∀ a : ℝ, 1 < a → a < 1+δ → ∀ x : ℝ,
        RiemannRealOrderFlow.flow a t (x : ℂ)=0 → |x| ≤ max 1 ((K/(a-1))^2) := by
  obtain ⟨δ,K,hδ,hδ4,hK,hbound⟩ := real_zero_transition_bound t ht
  refine ⟨δ,K,hδ,hδ4,hK,?_⟩
  intro a ha haδ x hz
  by_cases hx : 1 ≤ |x|
  · have hb := hbound a ha haδ x hx hz
    have hs : (|x|^(1/2 : ℝ))^2=|x| := by
      calc
        _ = (|x|^(1/2 : ℝ))^(2 : ℝ) := (Real.rpow_natCast _ 2).symm
        _ = |x|^((1/2 : ℝ)*2) := (Real.rpow_mul (abs_nonneg x) _ _).symm
        _ = _ := by norm_num
    have hp : 0 ≤ (a-1)*|x|^(1/2 : ℝ) :=
      mul_nonneg (sub_pos.mpr ha).le (Real.rpow_nonneg (abs_nonneg x) _)
    have hsq := pow_le_pow_left₀ hp hb 2
    rw [mul_pow,hs] at hsq
    have hr : |x| ≤ (K/(a-1))^2 := by
      rw [div_pow]
      exact (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr ha))).mpr (by nlinarith [hsq])
    exact hr.trans (le_max_right _ _)
  · exact (le_of_not_ge hx).trans (le_max_left _ _)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderTransitionRate
