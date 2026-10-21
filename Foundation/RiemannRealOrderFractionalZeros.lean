import Foundation.RiemannRealOrderFractionalReconstruction
import Foundation.RiemannRealOrderComplexZeros
import Foundation.RiemannRealOrderZeroLimits

/-! Actual nonreal zeros arbitrarily close to quadratic order, at nonzero time.
Escape for every selected sequence retains explicit hypotheses on the quadratic limit. -/
noncomputable section
open Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalZeros
open RiemannRealOrderFlow RiemannRealOrderFractionalReconstruction

theorem eventually_nonzero_atTop (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) (ht : t ≠ 0) :
    ∀ᶠ x : ℝ in atTop, flow a t (x : ℂ) ≠ 0 := by
  filter_upwards [RiemannRealOrderFractionalFourier.eventually_thirdSine_time_signed_positive
    a t ha ha3 ht] with x hx
  intro hz
  rw [← actual_third_identity a t x ha (by linarith),hz,mul_zero,Complex.zero_re,mul_zero] at hx
  exact (lt_irrefl 0) hx

theorem eventually_nonzero_cocompact (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) (ht : t ≠ 0) :
    ∀ᶠ x : ℝ in cocompact ℝ, flow a t (x : ℂ) ≠ 0 := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp (eventually_nonzero_atTop a t ha ha3 ht)
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

theorem compact_zero_set_finite (a t : ℝ) (ha : 0 ≤ a) (K : Set ℂ) (hK : IsCompact K) :
    (K ∩ (flow a t) ⁻¹' {0}).Finite := by
  let F : ℂ → ℂ := flow a t
  have hF : AnalyticOnNhd ℂ F univ :=
    (flow_differentiable a ha t).differentiableOn.analyticOnNhd isOpen_univ
  have hn : F 0 ≠ 0 := by
    have hp := actual_flow_zero_pos a ha t
    intro hz
    change flow a t 0=0 at hz
    rw [hz,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hm0 : meromorphicOrderAt F 0 ≠ ⊤ := by
    rw [(hF 0 (mem_univ _)).meromorphicOrderAt_eq,
      (hF 0 (mem_univ _)).analyticOrderAt_eq_zero.mpr hn]
    simp
  have horder (z : ℂ) : meromorphicOrderAt F z ≠ ⊤ :=
    (hF.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).mp
      ⟨⟨0,mem_univ _⟩,hm0⟩ ⟨z,mem_univ _⟩
  have hlocal := hF.mono (subset_univ K)
  rw [hlocal.meromorphicNFOn.zero_set_eq_divisor_support (fun z => horder z)]
  exact (MeromorphicOn.divisor F K).finiteSupport hK

theorem real_zero_set_finite (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) (ht : t ≠ 0) :
    {x : ℝ | flow a t (x : ℂ)=0}.Finite := by
  let F : ℂ → ℂ := flow a t
  have he : {x : ℝ | F (x : ℂ) ≠ 0} ∈ cocompact ℝ :=
    eventually_nonzero_cocompact a t ha ha3 ht
  obtain ⟨K,hK,hsub⟩ := mem_cocompact'.mp he
  let L : Set ℂ := Complex.ofReal '' K
  have hL : IsCompact L := hK.image Complex.continuous_ofReal
  have hZ : (L ∩ F ⁻¹' {0}).Finite := compact_zero_set_finite a t (by linarith) L hL
  have hpre : (Complex.ofReal ⁻¹' (L ∩ F ⁻¹' {0})).Finite :=
    Set.Finite.preimage (fun x _ y _ h => Complex.ofReal_injective h) hZ
  apply hpre.subset
  intro x hx
  change F (x : ℂ)=0 at hx
  have hxK : x ∈ K := hsub (by simpa only [mem_compl_iff,mem_setOf_eq,not_not] using hx)
  exact ⟨⟨x,hxK,rfl⟩,hx⟩

theorem nonreal_zero_set_infinite (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) (ht : t ≠ 0) :
    {z : ℂ | flow a t z=0 ∧ z.im≠0}.Infinite := by
  have hz := RiemannRealOrderComplexZeros.actual_complex_zero_set_infinite a (by linarith) t
  have hr := (real_zero_set_finite a t ha ha3 ht).image Complex.ofReal
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

theorem exists_nonreal_zero_norm_gt (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2)
    (ht : t ≠ 0) (R : ℝ) : ∃ z : ℂ, flow a t z=0 ∧ z.im≠0 ∧ R < ‖z‖ := by
  have hz := nonreal_zero_set_infinite a t ha ha3 ht
  have hc := compact_zero_set_finite a t (by linarith)
    (Metric.closedBall (0 : ℂ) R) (isCompact_closedBall ..)
  obtain ⟨z,hz,hnot⟩ := (hz.diff hc).nonempty
  refine ⟨z,hz.1,hz.2,?_⟩
  apply lt_of_not_ge
  intro hnorm
  apply hnot
  exact ⟨mem_closedBall_zero_iff.mpr hnorm,hz.1⟩

def approachingOrder (n : ℕ) : ℝ := 1+1/((n : ℝ)+3)

theorem approachingOrder_bounds (n : ℕ) : 1 < approachingOrder n ∧ approachingOrder n < 3/2 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  constructor
  · dsimp [approachingOrder]
    have hp : 0 < 1/((n : ℝ)+3) := by positivity
    linarith
  · have h : 1/((n : ℝ)+3) < (1/2 : ℝ) := (div_lt_iff₀ (by positivity)).mpr (by linarith)
    dsimp [approachingOrder]
    linarith

theorem approachingOrder_tendsto : Tendsto approachingOrder atTop (𝓝 (1 : ℝ)) := by
  change Tendsto (fun n : ℕ => 1+1/((n : ℝ)+3)) atTop (𝓝 (1 : ℝ))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat :
    Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 (0 : ℝ))).comp (tendsto_add_atTop_nat 2)
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).add h
  simpa only [approachingOrder,Function.comp_def,Nat.cast_add,Nat.cast_ofNat,
    add_assoc,show (2 : ℝ)+1=3 by norm_num,add_zero] using hh

theorem exists_approaching_nonreal_zeros (t : ℝ) (ht : t ≠ 0) :
    ∃ z : ℕ → ℂ, ∀ n, flow (approachingOrder n) t (z n)=0 ∧ (z n).im≠0 := by
  have h (n : ℕ) := (nonreal_zero_set_infinite (approachingOrder n) t
    (approachingOrder_bounds n).1 (approachingOrder_bounds n).2 ht).nonempty
  choose z hz using h
  exact ⟨z,hz⟩

theorem selected_nonreal_zeros_escape_of_quadratic_simple (t : ℝ)
    (hreal : ∀ w : ℂ, RiemannEvenFlow.flow 1 t w=0 → w.im=0)
    (hsimple : ∀ w : ℂ, RiemannEvenFlow.flow 1 t w=0 →
      deriv (RiemannEvenFlow.flow 1 t) w≠0) (z : ℕ → ℂ)
    (hz : ∀ n, flow (approachingOrder n) t (z n)=0 ∧ (z n).im≠0) :
    Tendsto (fun n => ‖z n‖) atTop atTop := by
  exact RiemannRealOrderZeroLimits.quadratic_nonreal_zero_escape t hreal hsimple
    approachingOrder z approachingOrder_tendsto (fun n => (hz n).1) (fun n => (hz n).2)

theorem exists_approaching_escaping_nonreal_zeros (t : ℝ) (ht : t ≠ 0) :
    ∃ z : ℕ → ℂ, (∀ n, flow (approachingOrder n) t (z n)=0 ∧ (z n).im≠0) ∧
      Tendsto (fun n => ‖z n‖) atTop atTop := by
  have h (n : ℕ) := exists_nonreal_zero_norm_gt (approachingOrder n) t
    (approachingOrder_bounds n).1 (approachingOrder_bounds n).2 ht (n : ℝ)
  choose z hz using h
  refine ⟨z,fun n => ⟨(hz n).1,(hz n).2.1⟩,?_⟩
  rw [Filter.tendsto_atTop]
  intro R
  filter_upwards [(tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ))
    atTop atTop).eventually (eventually_ge_atTop R)] with n hn
  exact hn.trans (hz n).2.2.le

theorem no_eventual_real_zeros (a : ℝ) (ha : 1 < a) (ha3 : a < 3/2) :
    ¬ ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∀ z : ℂ, flow a t z=0 → z.im=0 := by
  rintro ⟨T,hT⟩
  let t := max T 1
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  obtain ⟨z,hz,hi⟩ := (nonreal_zero_set_infinite a t ha ha3 ht.ne').nonempty
  exact hi (hT t (le_max_left _ _) z hz)

theorem no_split_polynomial_limit (a t : ℝ) (ha : 1 < a) (ha3 : a < 3/2) (ht : t ≠ 0) :
    ¬ ∃ P : ℕ → Polynomial ℝ, (∀ n, (P n).Splits) ∧ TendstoLocallyUniformlyOn
      (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) (flow a t) atTop univ := by
  rintro ⟨P,hP,hlim⟩
  have h0 : flow a t 0 ≠ 0 := by
    intro h
    have hp := actual_flow_zero_pos a (by linarith) t
    rw [h,Complex.zero_re] at hp
    exact (lt_irrefl 0) hp
  have hr := RealRootedVerticalLimit.real_zeros_of_locally_uniform_split_polynomials
    P (flow a t) (flow_differentiable a (by linarith) t) ⟨0,h0⟩ hP hlim
  obtain ⟨z,hz,hi⟩ := (nonreal_zero_set_infinite a t ha ha3 ht).nonempty
  exact hi (hr z hz)

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFractionalZeros
