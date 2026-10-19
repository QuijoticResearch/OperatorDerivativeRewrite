import Foundation.RiemannQuarticNormalizedAnalytic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Liouville
/-! A local real-zero criterion for conjugation-symmetric cosine perturbations.
The proof reuses Cauchy bounds and the verified scalar-ball lower estimate. -/
noncomputable section
open Set Metric Complex Filter
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticCosineLocalZeros

theorem norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (Complex.exp (z*Complex.I)) (Complex.exp (-z*Complex.I))
  rw [← Complex.two_cos,norm_mul,Complex.norm_ofNat,Complex.norm_exp,Complex.norm_exp] at h
  have h1 : (z*Complex.I).re= -z.im := by simp [Complex.mul_re]
  have h2 : (-z*Complex.I).re=z.im := by simp [Complex.mul_re]
  rw [h1,h2] at h
  have hneg := Real.exp_le_exp.mpr (neg_le_abs z.im)
  have hpos := Real.exp_le_exp.mpr (le_abs_self z.im)
  linarith

theorem norm_sin_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have h := norm_sub_le (Complex.exp (-z*Complex.I)) (Complex.exp (z*Complex.I))
  have hid : ‖Complex.exp (-z*Complex.I)-Complex.exp (z*Complex.I)‖=2*‖Complex.sin z‖ := by
    have he := congrArg norm (Complex.two_sin z)
    simpa only [norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one] using he.symm
  rw [hid,Complex.norm_exp,Complex.norm_exp] at h
  have h1 : (z*Complex.I).re= -z.im := by simp [Complex.mul_re]
  have h2 : (-z*Complex.I).re=z.im := by simp [Complex.mul_re]
  rw [h1,h2] at h
  have hneg := Real.exp_le_exp.mpr (neg_le_abs z.im)
  have hpos := Real.exp_le_exp.mpr (le_abs_self z.im)
  linarith

theorem trig_norm_le_three (a : ℝ) (w : ℂ) (hw : w ∈ closedBall (a : ℂ) 1) :
    ‖Complex.cos w‖ ≤ 3 ∧ ‖Complex.sin w‖ ≤ 3 := by
  have hd : ‖w-(a : ℂ)‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
  have hi := (Complex.abs_im_le_norm (w-(a : ℂ))).trans hd
  simp only [Complex.sub_im,Complex.ofReal_im,sub_zero] at hi
  have he : Real.exp |w.im| ≤ 3 := (Real.exp_le_exp.mpr hi).trans Real.exp_one_lt_three.le
  exact ⟨(norm_cos_le_exp_abs_im w).trans he,(norm_sin_le_exp_abs_im w).trans he⟩

theorem cos_lipschitz (a : ℝ) (w z : ℂ) (hw : w ∈ closedBall (a : ℂ) 1)
    (hz : z ∈ closedBall (a : ℂ) 1) : ‖Complex.cos z-Complex.cos w‖ ≤ 3*‖z-w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (fun v _ => Complex.differentiableAt_cos) ?_
    (convex_closedBall (a : ℂ) 1) hw hz
  intro v hv
  rw [Complex.deriv_cos,norm_neg]
  exact (trig_norm_le_three a v hv).2

theorem sin_lipschitz (a : ℝ) (w z : ℂ) (hw : w ∈ closedBall (a : ℂ) 1)
    (hz : z ∈ closedBall (a : ℂ) 1) : ‖Complex.sin z-Complex.sin w‖ ≤ 3*‖z-w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (fun v _ => Complex.differentiableAt_sin) ?_
    (convex_closedBall (a : ℂ) 1) hw hz
  intro v hv
  rw [Complex.deriv_sin]
  exact (trig_norm_le_three a v hv).1

theorem perturbation_deriv_bound (f : ℂ → ℂ) (hf : Differentiable ℂ f) (a : ℝ)
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
    (hf.sub Complex.differentiable_cos).differentiableOn.diffContOnCl_ball (Subset.refl _)
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ)<1/2)
    hd (fun v hv => hclose v (hsub (sphere_subset_closedBall hv)))
  change ‖deriv (f-Complex.cos) w‖ ≤ _ at h
  rw [deriv_sub (hf w) Complex.differentiableAt_cos] at h
  norm_num at h ⊢
  exact h

theorem real_simple_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hconj : ∀ w, f (conj w)=conj (f w)) (a : ℝ)
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
    have hpert := perturbation_deriv_bound f hf a hclose w hw
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
    (fun w _ => hf w) hbound z (conj z) hz hzc
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

end OperatorDerivativeRewrite.Foundation.RiemannQuarticCosineLocalZeros
