import Foundation.RiemannQuarticCosineLocalZeros
/-! Local-domain version of the existing cosine-perturbation criterion.
No entire extension of a locally holomorphic normalized flow is assumed. -/
noncomputable section
open Set Metric Complex Filter
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticLocalCosineZeros
open RiemannQuarticCosineLocalZeros

theorem perturbation_deriv_bound (f : ℂ → ℂ) (a : ℝ)
    (hf : ∀ w ∈ closedBall (a : ℂ) 1, DifferentiableAt ℂ f w)
    (hclose : ∀ v ∈ closedBall (a : ℂ) 1, ‖f v-Complex.cos v‖ ≤ 1/1000)
    (w : ℂ) (hw : w ∈ closedBall (a : ℂ) (1/1000)) :
    ‖deriv f w-deriv Complex.cos w‖ ≤ 1/500 := by
  have hsub : closedBall w (1/2) ⊆ closedBall (a : ℂ) 1 := by
    intro v hv
    have ht := dist_triangle v w (a : ℂ)
    have hw' := mem_closedBall.mp hw
    have hv' := mem_closedBall.mp hv
    apply mem_closedBall.mpr
    linarith
  have hd : DiffContOnCl ℂ (fun v => f v-Complex.cos v) (ball w (1/2)) :=
    (show DifferentiableOn ℂ (fun v => f v-Complex.cos v) (closedBall (a : ℂ) 1) from
      fun v hv => ((hf v hv).sub Complex.differentiableAt_cos).differentiableWithinAt).diffContOnCl_ball hsub
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ)<1/2)
    hd (fun v hv => hclose v (hsub (sphere_subset_closedBall hv)))
  change ‖deriv (f-Complex.cos) w‖ ≤ _ at h
  rw [deriv_sub (hf w (closedBall_subset_closedBall (by norm_num) hw)) Complex.differentiableAt_cos] at h
  norm_num at h ⊢
  exact h

theorem real_simple_zero (f : ℂ → ℂ) (a : ℝ)
    (hf : ∀ w ∈ closedBall (a : ℂ) 1, DifferentiableAt ℂ f w)
    (hconj : ∀ w, f (conj w)=conj (f w))
    (hclose : ∀ w ∈ closedBall (a : ℂ) 1, ‖f w-Complex.cos w‖ ≤ 1/1000)
    (z : ℂ) (hz : z ∈ closedBall (a : ℂ) (1/1000)) (hzero : f z=0) :
    z.im=0 ∧ deriv f z ≠ 0 := by
  have hz1 := closedBall_subset_closedBall (by norm_num : (1/1000 : ℝ) ≤ 1) hz
  have hzdist : ‖z-(a : ℂ)‖ ≤ (1/1000 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hz
  have hc := hclose z hz1
  rw [hzero,zero_sub,norm_neg] at hc
  have hcosvar := cos_lipschitz a (a : ℂ) z (mem_closedBall_self (by norm_num)) hz1
  have hnorm := norm_sub_le (Complex.cos z) (Complex.cos z-Complex.cos (a : ℂ))
  simp only [sub_sub_cancel] at hnorm
  have hcsmall : ‖Complex.cos (a : ℂ)‖ ≤ 1/250 := by linarith
  have hsin : 1/2 ≤ ‖Complex.sin (a : ℂ)‖ := by
    rw [← Complex.ofReal_cos,Complex.norm_real,Real.norm_eq_abs] at hcsmall
    rw [← Complex.ofReal_sin,Complex.norm_real,Real.norm_eq_abs]
    have hsq := Real.sin_sq_add_cos_sq a
    have hcabs := abs_nonneg (Real.cos a)
    have hsabs := abs_nonneg (Real.sin a)
    have hca := sq_abs (Real.cos a)
    have hsa := sq_abs (Real.sin a)
    nlinarith
  let d := -Complex.sin (a : ℂ)
  have hd : 1/2 ≤ ‖d‖ := by simpa only [d,norm_neg] using hsin
  have hbound : ∀ w ∈ closedBall (a : ℂ) (1/1000), ‖deriv f w-d‖ ≤ ‖d‖/2 := by
    intro w hw
    have hpert := perturbation_deriv_bound f a hf hclose w hw
    have hvar := sin_lipschitz a (a : ℂ) w (mem_closedBall_self (by norm_num))
      (closedBall_subset_closedBall (by norm_num) hw)
    have hwDist : ‖w-(a : ℂ)‖ ≤ (1/1000 : ℝ) := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have htri := norm_add_le (deriv f w-deriv Complex.cos w) (deriv Complex.cos w-d)
    simp only [sub_add_sub_cancel] at htri
    have hid : deriv Complex.cos w-d= -(Complex.sin w-Complex.sin (a : ℂ)) := by rw [Complex.deriv_cos]; dsimp [d]; ring
    rw [hid,norm_neg] at htri
    linarith
  have hzc : conj z ∈ closedBall (a : ℂ) (1/1000) := by
    have he : dist (conj z) (a : ℂ)=dist z (a : ℂ) := by
      rw [dist_eq_norm,dist_eq_norm,← Complex.conj_ofReal a,← map_sub,norm_conj,Complex.conj_ofReal]
    simpa only [mem_closedBall,he] using hz
  have hl := RiemannQuarticFrequencyBranch.scalar_ball_lower_bound f (a : ℂ) d (1/1000)
    (fun w hw => hf w (closedBall_subset_closedBall (by norm_num) hw)) hbound z (conj z) hz hzc
  rw [hconj,hzero,map_zero,sub_self,norm_zero] at hl
  have heq : z=conj z := by
    have hn : ‖z-conj z‖=0 := by nlinarith [norm_nonneg (z-conj z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hn)
  have hi := congrArg Complex.im heq
  simp only [Complex.conj_im] at hi
  refine ⟨by linarith,?_⟩
  intro hder
  have h := hbound z hz
  rw [hder,zero_sub,norm_neg] at h
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticLocalCosineZeros
