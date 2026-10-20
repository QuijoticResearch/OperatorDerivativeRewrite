import Foundation.RiemannRealOrderLimit
import Foundation.RiemannQuarticFrequencyBranch
import Foundation.RiemannQuarticGlobalSimpleZeros
import Mathlib.Topology.Sequences

/-! Joint order/spatial continuity for actual Fourier jets and zero limits.
No assertion about the zeros of the quadratic limit is assumed implicitly. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderZeroLimits
open RiemannRealOrderFlow RiemannRealOrderLimit

theorem jet_joint_continuousAt (a : ℝ) (ha : 0 < a) (j : ℕ) (t : ℝ) (z : ℂ) :
    ContinuousAt (fun p : ℝ × ℂ => jet p.1 j t p.2) (a,z) := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu := (Metric.tendstoUniformlyOn_iff.mp
    (jet_order_tendsto_uniformly_on_ball a ha j t R hR)) (ε/2) (half_pos hε)
  obtain ⟨δa,hδa,horder⟩ := Metric.eventually_nhds_iff.mp hu
  obtain ⟨δz,hδz,hspace⟩ := Metric.continuousAt_iff.mp
    (jet_hasDerivAt a ha.le j t z).continuousAt (ε/2) (half_pos hε)
  refine ⟨min δa (min δz 1),lt_min hδa (lt_min hδz (by norm_num)),?_⟩
  intro p hp
  have hpa : dist p.1 a < δa := (le_max_left _ _).trans_lt
    ((show max (dist p.1 a) (dist p.2 z) < min δa (min δz 1) from hp).trans_le (min_le_left _ _))
  have hpz : dist p.2 z < min δz 1 := (le_max_right _ _).trans_lt
    ((show max (dist p.1 a) (dist p.2 z) < min δa (min δz 1) from hp).trans_le (min_le_right _ _))
  have hball : p.2 ∈ closedBall (0 : ℂ) R := by
    have hn := norm_add_le (p.2-z) z
    rw [sub_add_cancel] at hn
    have hd : ‖p.2-z‖ < 1 := by
      simpa only [dist_eq_norm] using hpz.trans_le (min_le_right _ _)
    exact mem_closedBall_zero_iff.mpr (by dsimp [R]; linarith)
  have hparam : dist (jet p.1 j t p.2) (jet a j t p.2) < ε/2 := by
    simpa only [dist_comm] using horder hpa p.2 hball
  exact (dist_triangle _ (jet a j t p.2) _).trans_lt
    (by linarith [hparam,hspace (hpz.trans_le (min_le_left _ _))])

theorem flow_joint_continuousAt (a : ℝ) (ha : 0 < a) (t : ℝ) (z : ℂ) :
    ContinuousAt (fun p : ℝ × ℂ => flow p.1 t p.2) (a,z) := by
  have hp := jet_joint_continuousAt a ha 0 t z
  have hn := (jet_joint_continuousAt a ha 0 t (-z)).comp_of_eq
    (by fun_prop : ContinuousAt (fun p : ℝ × ℂ => (p.1,-p.2)) (a,z)) rfl
  change ContinuousAt (fun p : ℝ × ℂ => (jet p.1 0 t p.2+jet p.1 0 t (-p.2))/2) (a,z)
  simpa only [Function.comp_def,Pi.add_apply] using (hp.add hn).div_const (2 : ℂ)

theorem flow_deriv_eq (a : ℝ) (ha : 0 ≤ a) (t : ℝ) (z : ℂ) :
    deriv (flow a t) z = (jet a 1 t z-jet a 1 t (-z))/2 := by
  have h := ((jet_hasDerivAt a ha 0 t z).add
    ((jet_hasDerivAt a ha 0 t (-z)).comp z (hasDerivAt_neg z))).div_const 2
  change HasDerivAt (flow a t) ((jet a 1 t z+jet a 1 t (-z)*(-1))/2) z at h
  simpa only [mul_neg_one,sub_eq_add_neg] using h.deriv

theorem flow_deriv_joint_continuousAt (a : ℝ) (ha : 0 < a) (t : ℝ) (z : ℂ) :
    ContinuousAt (fun p : ℝ × ℂ => deriv (flow p.1 t) p.2) (a,z) := by
  have hp := jet_joint_continuousAt a ha 1 t z
  have hn := (jet_joint_continuousAt a ha 1 t (-z)).comp_of_eq
    (by fun_prop : ContinuousAt (fun p : ℝ × ℂ => (p.1,-p.2)) (a,z)) rfl
  have hc : ContinuousAt (fun p : ℝ × ℂ =>
      (jet p.1 1 t p.2-jet p.1 1 t (-p.2))/2) (a,z) := by
    simpa only [Function.comp_def,Pi.sub_apply] using (hp.sub hn).div_const (2 : ℂ)
  apply hc.congr_of_eventuallyEq
  have hb : ∀ᶠ p : ℝ × ℂ in 𝓝 (a,z), 0 < p.1 :=
    (continuous_fst.continuousAt.tendsto).eventually (Ioi_mem_nhds ha)
  filter_upwards [hb] with p hp
  exact flow_deriv_eq p.1 hp.le t p.2

theorem zero_of_order_and_zero_limits (a : ℝ) (ha : 0 < a) (t : ℝ)
    (s : ℕ → ℝ) (z : ℕ → ℂ) (w : ℂ)
    (hs : Tendsto s atTop (𝓝 a)) (hz : Tendsto z atTop (𝓝 w))
    (hzero : ∀ n, flow (s n) t (z n) = 0) : flow a t w = 0 := by
  have hc := (flow_joint_continuousAt a ha t w).tendsto.comp (hs.prodMk_nhds hz)
  apply tendsto_nhds_unique hc
  change Tendsto (fun n => flow (s n) t (z n)) atTop (𝓝 0)
  simpa only [hzero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

theorem derivative_zero_of_nonreal_order_limit (a : ℝ) (ha : 0 < a) (t : ℝ)
    (s : ℕ → ℝ) (z : ℕ → ℂ) (w : ℂ)
    (hs : Tendsto s atTop (𝓝 a)) (hz : Tendsto z atTop (𝓝 w))
    (hw : w.im = 0) (hzero : ∀ n, flow (s n) t (z n) = 0)
    (hnon : ∀ n, (z n).im ≠ 0) : deriv (flow a t) w = 0 := by
  by_contra hne
  let c := deriv (flow a t) w
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr hne
  obtain ⟨δ,hδ,hD⟩ := Metric.continuousAt_iff.mp
    (flow_deriv_joint_continuousAt a ha t w) (‖c‖/2) (half_pos hc)
  have horder : ∀ᶠ n : ℕ in atTop, dist (s n) a < δ :=
    (Metric.tendsto_nhds.mp hs) δ hδ
  have hpoint : ∀ᶠ n : ℕ in atTop, dist (z n) w < δ/2 :=
    (Metric.tendsto_nhds.mp hz) (δ/2) (half_pos hδ)
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < s n := hs.eventually (Ioi_mem_nhds ha)
  obtain ⟨n,hsclose,hzclose,hnpos⟩ := (horder.and (hpoint.and hpos)).exists
  have hd (q : ℂ) (_ : q ∈ closedBall w (δ/2)) : DifferentiableAt ℂ (flow (s n) t) q :=
    (flow_differentiable (s n) hnpos.le t) q
  have hb (q : ℂ) (hq : q ∈ closedBall w (δ/2)) :
      ‖deriv (flow (s n) t) q-c‖ ≤ ‖c‖/2 := by
    have hqdist : dist q w < δ := (mem_closedBall.mp hq).trans_lt (by linarith)
    have hp : dist (s n,q) (a,w) < δ := by rw [Prod.dist_eq]; exact max_lt hsclose hqdist
    exact (show ‖deriv (flow (s n) t) q-c‖ < ‖c‖/2 from by
      simpa only [dist_eq_norm] using hD hp).le
  have hwconj : conj w = w := by apply Complex.ext <;> simp [hw]
  have hconjdist : dist (conj (z n)) w = dist (z n) w := by
    have he : conj (z n)-w = conj (z n-w) := by simp [hwconj]
    simp only [dist_eq_norm,he,norm_conj]
  have hzn : z n ∈ closedBall w (δ/2) := mem_closedBall.mpr hzclose.le
  have hcn : conj (z n) ∈ closedBall w (δ/2) := by
    rw [mem_closedBall,hconjdist]
    exact hzclose.le
  have hbound := RiemannQuarticFrequencyBranch.scalar_ball_lower_bound
    (flow (s n) t) w c (δ/2) hd hb (z n) (conj (z n)) hzn hcn
  have hczero : flow (s n) t (conj (z n)) = 0 := by
    rw [flow_conj (s n) hnpos.le t,hzero n]
    simp
  rw [hzero n,hczero,sub_self,norm_zero] at hbound
  have hdiff : z n-conj (z n) ≠ 0 := by
    intro he
    have him := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.conj_im] at him
    exact hnon n (by linarith)
  exact (not_lt_of_ge hbound) (mul_pos (half_pos hc) (norm_pos_iff.mpr hdiff))

theorem eventually_real_zeros_on_compact (a : ℝ) (ha : 0 < a) (t : ℝ)
    (hreal : ∀ w : ℂ, flow a t w = 0 → w.im = 0)
    (hsimple : ∀ w : ℂ, flow a t w = 0 → deriv (flow a t) w ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ b : ℝ in 𝓝 a, ∀ w ∈ K, flow b t w = 0 → w.im = 0 := by
  classical
  by_contra h
  have hbad : ¬ ∃ δ > (0 : ℝ), ∀ b : ℝ, dist b a < δ →
      ∀ w ∈ K, flow b t w = 0 → w.im = 0 := by
    simpa only [Metric.eventually_nhds_iff] using h
  push_neg at hbad
  have hex (n : ℕ) : ∃ b : ℝ, ∃ w : ℂ, dist b a < 1/((n : ℝ)+1) ∧
      w ∈ K ∧ flow b t w = 0 ∧ w.im ≠ 0 := by
    obtain ⟨b,hb,w,hw,hzero,hi⟩ := hbad (1/((n : ℝ)+1)) (by positivity)
    exact ⟨b,w,hb,hw,hzero,hi⟩
  choose s z hdist hmem hzero hnon using hex
  have hs : Tendsto s atTop (𝓝 a) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [(tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 (0 : ℝ))).eventually
      (gt_mem_nhds hε)] with n hn
    exact (hdist n).trans hn
  obtain ⟨w,_,φ,hφ,hw⟩ := hK.tendsto_subseq hmem
  have horder := hs.comp hφ.tendsto_atTop
  have hwzero := zero_of_order_and_zero_limits a ha t (s ∘ φ) (z ∘ φ) w
    horder hw (fun n => hzero (φ n))
  have hder := derivative_zero_of_nonreal_order_limit a ha t (s ∘ φ) (z ∘ φ) w
    horder hw (hreal w hwzero) (fun n => hzero (φ n)) (fun n => hnon (φ n))
  exact hsimple w hwzero hder

theorem nonreal_zero_norm_tendsto_atTop (a : ℝ) (ha : 0 < a) (t : ℝ)
    (hreal : ∀ w : ℂ, flow a t w = 0 → w.im = 0)
    (hsimple : ∀ w : ℂ, flow a t w = 0 → deriv (flow a t) w ≠ 0)
    (s : ℕ → ℝ) (z : ℕ → ℂ) (hs : Tendsto s atTop (𝓝 a))
    (hzero : ∀ n, flow (s n) t (z n) = 0) (hnon : ∀ n, (z n).im ≠ 0) :
    Tendsto (fun n => ‖z n‖) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro R
  have he := eventually_real_zeros_on_compact a ha t hreal hsimple
    (closedBall (0 : ℂ) R) (isCompact_closedBall ..)
  filter_upwards [hs.eventually he] with n hn
  by_contra hR
  have hz : z n ∈ closedBall (0 : ℂ) R :=
    mem_closedBall_zero_iff.mpr (le_of_lt (lt_of_not_ge hR))
  exact hnon n (hn (z n) hz (hzero n))

theorem quadratic_compact_zero_stability (t : ℝ)
    (hreal : ∀ w : ℂ, RiemannEvenFlow.flow 1 t w = 0 → w.im = 0)
    (hsimple : ∀ w : ℂ, RiemannEvenFlow.flow 1 t w = 0 →
      deriv (RiemannEvenFlow.flow 1 t) w ≠ 0) (K : Set ℂ) (hK : IsCompact K) :
    ∀ᶠ b : ℝ in 𝓝 (1 : ℝ), ∀ w ∈ K, flow b t w = 0 → w.im = 0 := by
  have he : flow (1 : ℝ) t = RiemannEvenFlow.flow 1 t := by
    funext w
    simpa only [Nat.cast_one] using flow_nat 1 t w
  apply eventually_real_zeros_on_compact 1 (by norm_num) t
  · simpa only [he] using hreal
  · simpa only [he] using hsimple
  · exact hK

theorem quadratic_nonreal_zero_escape (t : ℝ)
    (hreal : ∀ w : ℂ, RiemannEvenFlow.flow 1 t w = 0 → w.im = 0)
    (hsimple : ∀ w : ℂ, RiemannEvenFlow.flow 1 t w = 0 →
      deriv (RiemannEvenFlow.flow 1 t) w ≠ 0)
    (s : ℕ → ℝ) (z : ℕ → ℂ) (hs : Tendsto s atTop (𝓝 (1 : ℝ)))
    (hzero : ∀ n, flow (s n) t (z n) = 0) (hnon : ∀ n, (z n).im ≠ 0) :
    Tendsto (fun n => ‖z n‖) atTop atTop := by
  have he : flow (1 : ℝ) t = RiemannEvenFlow.flow 1 t := by
    funext w
    simpa only [Nat.cast_one] using flow_nat 1 t w
  apply nonreal_zero_norm_tendsto_atTop 1 (by norm_num) t ?_ ?_ s z hs hzero hnon
  · simpa only [he] using hreal
  · simpa only [he] using hsimple

theorem eventually_quartic_order_compact_stability :
    ∀ᶠ t : ℝ in atTop, ∀ K : Set ℂ, IsCompact K →
      ∀ᶠ b : ℝ in 𝓝 (2 : ℝ), ∀ w ∈ K, flow b t w = 0 → w.im = 0 := by
  filter_upwards [RiemannQuarticGlobalSimpleZeros.eventually_all_zeros_real_simple] with t ht
  intro K hK
  have he : flow (2 : ℝ) t = RiemannQuarticFlow.flow t := by
    funext w
    simpa only [Nat.cast_ofNat,RiemannEvenFlow.flow_quartic] using flow_nat 2 t w
  have hr : ∀ w : ℂ, RiemannQuarticFlow.flow t w = 0 → w.im = 0 := fun w hz => (ht w hz).1
  have hd : ∀ w : ℂ, RiemannQuarticFlow.flow t w = 0 →
      deriv (RiemannQuarticFlow.flow t) w ≠ 0 := fun w hz => (ht w hz).2
  apply eventually_real_zeros_on_compact 2 (by norm_num) t ?_ ?_ K hK
  · simpa only [he] using hr
  · simpa only [he] using hd

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderZeroLimits
