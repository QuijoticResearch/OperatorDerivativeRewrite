import Foundation.RiemannQuarticThresholdCompactness
import Foundation.RiemannQuarticGlobalSimpleZeros
import Foundation.RiemannQuarticZeroCounting

/-! Genuine collision at the attained quartic threshold. Joint continuity
of the actual spatial derivative and an existing local lower bound exclude
convergence of conjugate distinct zeros to a simple real zero. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdCollision
open RiemannQuarticFlow RiemannQuarticEvolution RiemannQuarticOpenObstruction

theorem flow_deriv_eq (t : ℝ) (z : ℂ) :
    deriv (flow t) z = (jet 1 t z-jet 1 t (-z))/2 := by
  have h := congrFun (flow_iteratedDeriv 1 t) z
  simpa [symmetricJet,sub_eq_add_neg] using h

theorem flow_deriv_joint_continuous :
    Continuous (fun p : ℝ × ℂ => deriv (flow p.1) p.2) := by
  have hn : Continuous (fun p : ℝ × ℂ => (p.1,-p.2)) := by fun_prop
  have hj := RiemannQuarticTimeCompact.jet_joint_continuous 1
  simpa only [flow_deriv_eq,Pi.sub_apply,Function.comp_apply] using
    (hj.sub (hj.comp hn)).div_const 2

theorem derivative_zero_of_nonreal_zero_limit (s : ℕ → ℝ) (z : ℕ → ℂ)
    (τ : ℝ) (w : ℂ) (hs : Tendsto s atTop (𝓝 τ)) (hz : Tendsto z atTop (𝓝 w))
    (hw : w.im = 0) (hzero : ∀ n, flow (s n) (z n) = 0)
    (hnon : ∀ n, (z n).im ≠ 0) : deriv (flow τ) w = 0 := by
  by_contra hne
  let c := deriv (flow τ) w
  have hc : 0 < ‖c‖ := norm_pos_iff.mpr hne
  have hcont : ContinuousAt (fun p : ℝ × ℂ => deriv (flow p.1) p.2) (τ,w) :=
    flow_deriv_joint_continuous.continuousAt
  obtain ⟨δ,hδ,hD⟩ := Metric.continuousAt_iff.mp hcont (‖c‖/2) (half_pos hc)
  have htime : ∀ᶠ n : ℕ in atTop, dist (s n) τ < δ :=
    (Metric.tendsto_nhds.mp hs) δ hδ
  have hpoint : ∀ᶠ n : ℕ in atTop, dist (z n) w < δ/2 :=
    (Metric.tendsto_nhds.mp hz) (δ/2) (half_pos hδ)
  obtain ⟨n,ht,hzclose⟩ := (htime.and hpoint).exists
  have hd (q : ℂ) (_ : q ∈ closedBall w (δ/2)) : DifferentiableAt ℂ (flow (s n)) q :=
    (flow_differentiable (s n)) q
  have hb (q : ℂ) (hq : q ∈ closedBall w (δ/2)) :
      ‖deriv (flow (s n)) q-c‖ ≤ ‖c‖/2 := by
    have hqdist : dist q w < δ := (mem_closedBall.mp hq).trans_lt (by linarith)
    have hp : dist (s n,q) (τ,w) < δ := by
      rw [Prod.dist_eq]
      exact max_lt ht hqdist
    have hh : ‖deriv (flow (s n)) q-c‖ < ‖c‖/2 := by
      simpa only [dist_eq_norm] using hD hp
    exact hh.le
  have hwconj : conj w = w := by apply Complex.ext <;> simp [hw]
  have hconjdist : dist (conj (z n)) w = dist (z n) w := by
    have he : conj (z n)-w = conj (z n-w) := by simp [hwconj]
    simp only [dist_eq_norm,he,norm_conj]
  have hzn : z n ∈ closedBall w (δ/2) := mem_closedBall.mpr hzclose.le
  have hcn : conj (z n) ∈ closedBall w (δ/2) := by
    rw [mem_closedBall,hconjdist]
    exact hzclose.le
  have hbound := RiemannQuarticFrequencyBranch.scalar_ball_lower_bound
    (flow (s n)) w c (δ/2) hd hb (z n) (conj (z n)) hzn hcn
  have hczero : flow (s n) (conj (z n)) = 0 := by
    rw [RiemannQuarticNormalizedAnalytic.flow_conj,hzero n]
    simp
  rw [hzero n,hczero,sub_self,norm_zero] at hbound
  have hdiff : z n-conj (z n) ≠ 0 := by
    intro he
    have him := congrArg Complex.im (sub_eq_zero.mp he)
    simp only [Complex.conj_im] at him
    exact hnon n (by linarith)
  have hp := mul_pos (half_pos hc) (norm_pos_iff.mpr hdiff)
  exact (not_lt_of_ge hbound) hp

theorem exists_real_multiple_zero_at_threshold :
    ∃ w : ℂ, w.im = 0 ∧ flow (sInf polynomialLimitStarts) w = 0 ∧
      deriv (flow (sInf polynomialLimitStarts)) w = 0 := by
  obtain ⟨s,z,w,hs,hz,hdata,hwzero,hwreal⟩ :=
    RiemannQuarticThresholdCompactness.exists_convergent_nonreal_zeros_before_threshold
  exact ⟨w,hwreal,hwzero,derivative_zero_of_nonreal_zero_limit s z
    (sInf polynomialLimitStarts) w hs hz hwreal (fun n => (hdata n).2.1)
      (fun n => (hdata n).2.2)⟩

theorem exists_positive_finite_multiple_zero_at_threshold :
    ∃ x : ℝ, 0 < x ∧ flow (sInf polynomialLimitStarts) (x : ℂ) = 0 ∧
      deriv (flow (sInf polynomialLimitStarts)) (x : ℂ) = 0 ∧
      2 ≤ analyticOrderAt (flow (sInf polynomialLimitStarts)) (x : ℂ) ∧
      analyticOrderAt (flow (sInf polynomialLimitStarts)) (x : ℂ) ≠ ⊤ := by
  let A := sInf polynomialLimitStarts
  obtain ⟨w,hw,hzero,hderiv⟩ := exists_real_multiple_zero_at_threshold
  have hwcoe : (w.re : ℂ) = w := by apply Complex.ext <;> simp [hw]
  have hnon : w ≠ 0 := by
    intro he
    have hn := RiemannQuarticReality.flow_ne_zero_on_imaginary_axis A 0
    apply hn
    simpa only [he,Complex.ofReal_zero,mul_zero] using hzero
  have hxne : w.re ≠ 0 := by
    intro he
    apply hnon
    rw [← hwcoe,he]
    simp
  have hex : ∃ x : ℝ, 0 < x ∧ flow A (x : ℂ) = 0 ∧ deriv (flow A) (x : ℂ) = 0 := by
    rcases lt_or_gt_of_ne hxne with hneg | hpos
    · refine ⟨-w.re,by linarith,?_,?_⟩
      · rw [Complex.ofReal_neg,hwcoe,RiemannQuarticEvolution.flow_even]
        exact hzero
      · rw [Complex.ofReal_neg,hwcoe,RiemannQuarticGlobalSimpleZeros.deriv_flow_neg,hderiv,neg_zero]
    · exact ⟨w.re,hpos,by simpa only [hwcoe] using hzero,by simpa only [hwcoe] using hderiv⟩
  obtain ⟨x,hx,hz,hd⟩ := hex
  have ha : AnalyticAt ℂ (flow A) (x : ℂ) := (flow_differentiable A).analyticAt _
  have horder : 2 ≤ analyticOrderAt (flow A) (x : ℂ) := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero ha).mpr
    intro i hi
    interval_cases i <;> simp [hz,hd]
  have hfinite : analyticOrderAt (flow A) (x : ℂ) ≠ ⊤ := by
    intro h
    have hm := RiemannQuarticZeroCounting.flow_zero_order_finite A (x : ℂ)
    rw [ha.meromorphicOrderAt_eq,h] at hm
    simp at hm
  exact ⟨x,hx,hz,hd,horder,hfinite⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticThresholdCollision
