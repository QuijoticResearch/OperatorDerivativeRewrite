import Foundation.RiemannRealOrderFourthAsymptotic
import Foundation.RiemannRealOrderFractionalZeros

/-! Nonreal fractional zeros approaching the late real/simple quartic flow.
No quadratic zero-reality or Riemann hypothesis assumption is used. -/
noncomputable section
open Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderQuarticLimitZeros
open RiemannRealOrderFlow RiemannRealOrderFractionalCoefficient RiemannRealOrderFourthAsymptotic

theorem eventually_nonzero_atTop (a t : ℝ) (ha : 3/2 < a) (ha2 : a < 2) (ht : t ≠ 0) :
    ∀ᶠ x : ℝ in atTop, flow a t (x : ℂ)≠0 := by
  have hL : (leading a t : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (leading_ne_zero a t (by linarith) ha2 ht)
  have he := (actual_flow_scaled_limit a t ha ha2).eventually (eventually_ne_nhds hL)
  filter_upwards [he] with x hx
  intro hz
  apply hx
  rw [hz,mul_zero]

theorem eventually_nonzero_cocompact (a t : ℝ) (ha : 3/2 < a) (ha2 : a < 2) (ht : t ≠ 0) :
    ∀ᶠ x : ℝ in cocompact ℝ, flow a t (x : ℂ)≠0 := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp (eventually_nonzero_atTop a t ha ha2 ht)
  apply mem_cocompact'.mpr
  refine ⟨Icc (-R) R,isCompact_Icc,?_⟩
  intro x hx
  have hz : flow a t (x : ℂ)=0 := by simpa using hx
  constructor
  · by_contra h
    have hn := hR (-x) (by linarith : R ≤ -x)
    apply hn
    rw [Complex.ofReal_neg,flow_even]
    exact hz
  · by_contra h
    exact hR x (by linarith) hz

theorem real_zero_set_finite (a t : ℝ) (ha : 3/2 < a) (ha2 : a < 2) (ht : t ≠ 0) :
    {x : ℝ | flow a t (x : ℂ)=0}.Finite := by
  let F : ℂ → ℂ := flow a t
  have he : {x : ℝ | F (x : ℂ)≠0} ∈ cocompact ℝ := eventually_nonzero_cocompact a t ha ha2 ht
  obtain ⟨K,hK,hsub⟩ := mem_cocompact'.mp he
  let L : Set ℂ := Complex.ofReal '' K
  have hL : IsCompact L := hK.image Complex.continuous_ofReal
  have hZ : (L ∩ F ⁻¹' {0}).Finite :=
    RiemannRealOrderFractionalZeros.compact_zero_set_finite a t (by linarith) L hL
  have hpre : (Complex.ofReal ⁻¹' (L ∩ F ⁻¹' {0})).Finite :=
    Set.Finite.preimage (fun x _ y _ h => Complex.ofReal_injective h) hZ
  apply hpre.subset
  intro x hx
  change F (x : ℂ)=0 at hx
  have hxK : x ∈ K := hsub (by simpa only [mem_compl_iff,mem_setOf_eq,not_not] using hx)
  exact ⟨⟨x,hxK,rfl⟩,hx⟩

theorem nonreal_zero_set_infinite (a t : ℝ) (ha : 3/2 < a) (ha2 : a < 2) (ht : t ≠ 0) :
    {z : ℂ | flow a t z=0 ∧ z.im≠0}.Infinite := by
  have hz := RiemannRealOrderComplexZeros.actual_complex_zero_set_infinite a (by linarith) t
  have hr := (real_zero_set_finite a t ha ha2 ht).image Complex.ofReal
  apply (hz.diff hr).mono
  rintro z ⟨hzero,hnot⟩
  refine ⟨hzero,?_⟩
  intro him
  have hcoe : (z.re : ℂ)=z := by apply Complex.ext <;> simp [him]
  apply hnot
  refine ⟨z.re,?_,hcoe⟩
  change flow a t (z.re : ℂ)=0
  rw [hcoe]
  exact hzero

theorem exists_nonreal_zero_norm_gt (a t : ℝ) (ha : 3/2 < a) (ha2 : a < 2)
    (ht : t ≠ 0) (R : ℝ) : ∃ z : ℂ, flow a t z=0 ∧ z.im≠0 ∧ R < ‖z‖ := by
  have hz := nonreal_zero_set_infinite a t ha ha2 ht
  have hc := RiemannRealOrderFractionalZeros.compact_zero_set_finite a t (by linarith)
    (Metric.closedBall (0 : ℂ) R) (isCompact_closedBall ..)
  obtain ⟨z,hz,hnot⟩ := (hz.diff hc).nonempty
  refine ⟨z,hz.1,hz.2,?_⟩
  apply lt_of_not_ge
  intro hnorm
  apply hnot
  exact ⟨mem_closedBall_zero_iff.mpr hnorm,hz.1⟩

def approachingQuarticOrder (n : ℕ) : ℝ := 2-1/((n : ℝ)+3)

theorem approachingQuarticOrder_bounds (n : ℕ) :
    3/2 < approachingQuarticOrder n ∧ approachingQuarticOrder n < 2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < 1/((n : ℝ)+3) := by positivity
  have hu : 1/((n : ℝ)+3) < (1/2 : ℝ) := (div_lt_iff₀ (by positivity)).mpr (by linarith)
  constructor <;> dsimp [approachingQuarticOrder] <;> linarith

theorem approachingQuarticOrder_tendsto : Tendsto approachingQuarticOrder atTop (𝓝 (2 : ℝ)) := by
  change Tendsto (fun n : ℕ => 2-1/((n : ℝ)+3)) atTop (𝓝 (2 : ℝ))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 (0 : ℝ))).comp (tendsto_add_atTop_nat 2)
  have hh := (tendsto_const_nhds (x := (2 : ℝ))).sub h
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_ofNat,add_assoc,
    show (2 : ℝ)+1=3 by norm_num,sub_zero] using hh

theorem exists_quartic_approaching_nonreal_zeros (t : ℝ) (ht : t ≠ 0) :
    ∃ z : ℕ → ℂ, ∀ n, flow (approachingQuarticOrder n) t (z n)=0 ∧ (z n).im≠0 := by
  have h (n : ℕ) := (nonreal_zero_set_infinite (approachingQuarticOrder n) t
    (approachingQuarticOrder_bounds n).1 (approachingQuarticOrder_bounds n).2 ht).nonempty
  choose z hz using h
  exact ⟨z,hz⟩

theorem eventually_quartic_selected_nonreal_escape :
    ∀ᶠ t : ℝ in atTop, ∀ s : ℕ → ℝ, ∀ z : ℕ → ℂ, Tendsto s atTop (𝓝 (2 : ℝ)) →
      (∀ n, flow (s n) t (z n)=0) → (∀ n, (z n).im≠0) →
        Tendsto (fun n => ‖z n‖) atTop atTop := by
  filter_upwards [RiemannRealOrderZeroLimits.eventually_quartic_order_compact_stability] with t ht
  intro s z hs hz hnon
  rw [Filter.tendsto_atTop]
  intro R
  have he := ht (Metric.closedBall (0 : ℂ) R) (isCompact_closedBall ..)
  filter_upwards [hs.eventually he] with n hn
  by_contra hR
  have hnorm : z n ∈ Metric.closedBall (0 : ℂ) R :=
    mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge hR))
  exact hnon n (hn (z n) hnorm (hz n))

theorem eventually_quartic_real_simple_with_escaping_fractional_zeros :
    ∀ᶠ t : ℝ in atTop,
      (∀ w : ℂ, flow 2 t w=0 → w.im=0 ∧ deriv (flow 2 t) w≠0) ∧
      ∃ z : ℕ → ℂ, (∀ n, flow (approachingQuarticOrder n) t (z n)=0 ∧ (z n).im≠0) ∧
        Tendsto (fun n => ‖z n‖) atTop atTop := by
  filter_upwards [RiemannQuarticGlobalSimpleZeros.eventually_all_zeros_real_simple,
    eventually_quartic_selected_nonreal_escape,eventually_gt_atTop (0 : ℝ)] with t hq he ht
  have hflow : flow (2 : ℝ) t=RiemannQuarticFlow.flow t := by
    funext w
    simpa only [Nat.cast_ofNat,RiemannEvenFlow.flow_quartic] using flow_nat 2 t w
  refine ⟨?_,?_⟩
  · simpa only [hflow] using hq
  · obtain ⟨z,hz⟩ := exists_quartic_approaching_nonreal_zeros t ht.ne'
    exact ⟨z,hz,he approachingQuarticOrder z approachingQuarticOrder_tendsto
      (fun n => (hz n).1) (fun n => (hz n).2)⟩

theorem between_one_two_real_zeros_finite (a t : ℝ) (ha : 1 < a) (ha2 : a < 2) (ht : t ≠ 0) :
    {x : ℝ | flow a t (x : ℂ)=0}.Finite := by
  rcases lt_trichotomy a (3/2) with h | h | h
  · exact RiemannRealOrderFractionalZeros.real_zero_set_finite a t ha h ht
  · subst a
    exact RiemannRealOrderCubicEndpoint.actual_real_zero_set_finite t ht
  · exact real_zero_set_finite a t h ha2 ht

theorem between_one_two_nonreal_zeros_infinite (a t : ℝ) (ha : 1 < a) (ha2 : a < 2) (ht : t ≠ 0) :
    {z : ℂ | flow a t z=0 ∧ z.im≠0}.Infinite := by
  rcases lt_trichotomy a (3/2) with h | h | h
  · exact RiemannRealOrderFractionalZeros.nonreal_zero_set_infinite a t ha h ht
  · subst a
    exact RiemannRealOrderComplexZeros.three_halves_nonreal_zero_set_infinite t ht
  · exact nonreal_zero_set_infinite a t h ha2 ht

theorem between_one_two_no_eventual_real_zeros (a : ℝ) (ha : 1 < a) (ha2 : a < 2) :
    ¬ ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ z : ℂ, flow a t z=0 → z.im=0 := by
  rintro ⟨T,hT⟩
  let t := max T 1
  have ht : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  obtain ⟨z,hz,hi⟩ := (between_one_two_nonreal_zeros_infinite a t ha ha2 ht.ne').nonempty
  exact hi (hT t (le_max_left _ _) z hz)

theorem between_one_two_no_split_polynomial_limit (a t : ℝ) (ha : 1 < a) (ha2 : a < 2)
    (ht : t ≠ 0) :
    ¬ ∃ P : ℕ → Polynomial ℝ, (∀ n, (P n).Splits) ∧ TendstoLocallyUniformlyOn
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow a t) atTop univ := by
  rintro ⟨P,hP,hlim⟩
  have h0 : flow a t 0≠0 := by
    intro h
    have hp := actual_flow_zero_pos a (by linarith) t
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hr := RealRootedVerticalLimit.real_zeros_of_locally_uniform_split_polynomials
    P (flow a t) (flow_differentiable a (by linarith) t) ⟨0,h0⟩ hP hlim
  obtain ⟨z,hz,hi⟩ := (between_one_two_nonreal_zeros_infinite a t ha ha2 ht).nonempty
  exact hi (hr z hz)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderQuarticLimitZeros
