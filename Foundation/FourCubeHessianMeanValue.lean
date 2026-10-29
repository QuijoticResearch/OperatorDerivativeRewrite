import Foundation.FourCubeMixedMeanValue

/-! Actual two-face mixed Hessian comparison from the full-Haar corner response. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourCubeHessianMeanValue
open FourCubeHaarContinuousIntegral FourCubeBoundarySmoothPartition
open FourCubeMixedMeanValue FourCubeThermalMixedDifference

private theorem mean (f df : ℝ → ℝ) (hd : ∀ x,HasDerivAt f (df x) x) (h : ℝ) (hh : 0<h) :
    ∃ x∈Ioo (-h) h, df x=(f h-f (-h))/(2*h) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  simpa only [sub_neg_eq_add,← two_mul] using
    exists_hasDerivAt_eq_slope f df (show -h<h by linarith) hc.continuousOn (fun x _ => hd x)

theorem two_face_mean (F : Parameters → ℝ) (hF : ContDiff ℝ ∞ F) (h : ℝ) (hh : 0<h) :
    ∃ x∈Ioo (-h) h, ∃ y∈Ioo (-h) h,
      spatialPartial 1 (spatialPartial 0 F) ![x,y,h]-
        spatialPartial 1 (spatialPartial 0 F) ![x,y,-h]=
        cornerSum (fun x y z => F ![x,y,z]) h/(4*h^2) := by
  have h0 := partial_contDiff 0 F hF
  let A := fun x => F ![x,h,h]-F ![x,-h,h]-F ![x,h,-h]+F ![x,-h,-h]
  let A' := fun x => spatialPartial 0 F ![x,h,h]-spatialPartial 0 F ![x,-h,h]-
    spatialPartial 0 F ![x,h,-h]+spatialPartial 0 F ![x,-h,-h]
  have hA (x : ℝ) : HasDerivAt A (A' x) x :=
    ((((slice_x F hF x h h).sub (slice_x F hF x (-h) h)).sub
      (slice_x F hF x h (-h))).add (slice_x F hF x (-h) (-h)))
  obtain ⟨x,hx,hAx⟩ := mean A A' hA h hh
  let B := fun y => spatialPartial 0 F ![x,y,h]-spatialPartial 0 F ![x,y,-h]
  let B' := fun y => spatialPartial 1 (spatialPartial 0 F) ![x,y,h]-spatialPartial 1 (spatialPartial 0 F) ![x,y,-h]
  have hB (y : ℝ) : HasDerivAt B (B' y) y :=
    (slice_y _ h0 x y h).sub (slice_y _ h0 x y (-h))
  obtain ⟨y,hy,hBy⟩ := mean B B' hB h hh
  refine ⟨x,hx,y,hy,?_⟩
  have heB : B h-B (-h)=A' x := by dsimp [B,A']; ring
  have heA : A h-A (-h)=cornerSum (fun x y z => F ![x,y,z]) h := by dsimp [A,cornerSum]; ring
  change spatialPartial 1 (spatialPartial 0 F) ![x,y,h]-
    spatialPartial 1 (spatialPartial 0 F) ![x,y,-h]=_ at hBy
  rw [heB,hAx,heA] at hBy
  rw [hBy]
  field_simp [hh.ne']
  <;> ring

def mixedHessian (β x y z : ℝ) : ℝ :=
  spatialPartial 1 (spatialPartial 0 (FourCubeBoundarySmoothPartition.freeEnergy β)) ![x,y,z]

theorem actual_two_face_mean (β h : ℝ) (hh : 0<h) :
    ∃ x y : ℝ,|x|<h ∧ |y|<h ∧ mixedHessian β x y h-mixedHessian β x y (-h)=2*h*difference β h := by
  obtain ⟨x,hx,y,hy,he⟩ := two_face_mean (FourCubeBoundarySmoothPartition.freeEnergy β)
    (actual_freeEnergy_contDiff β) h hh
  refine ⟨x,y,abs_lt.mpr hx,abs_lt.mpr hy,?_⟩
  change mixedHessian β x y h-mixedHessian β x y (-h)=_ at he
  have hf : (fun x y z => FourCubeBoundarySmoothPartition.freeEnergy β ![x,y,z])=
      FourCubeThermalMixedDifference.freeEnergy β := by funext x y z; rfl
  rw [hf] at he
  rw [he]
  unfold difference
  field_simp [hh.ne']
  <;> ring

theorem actual_thermal_hessian_difference :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ x y : ℝ,|x|<t ∧ |y|<t ∧
      c/t < mixedHessian (1/t^2) x y t-mixedHessian (1/t^2) x y (-t) := by
  have hm : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (by intro t ht; exact ne_of_gt ht)
  filter_upwards [actual_third_difference_lower.filter_mono hm,self_mem_nhdsWithin] with t ht htpos
  have ht0 : 0<t := htpos
  obtain ⟨x,y,hx,hy,he⟩ := actual_two_face_mean (1/t^2) t ht0
  refine ⟨x,y,hx,hy,?_⟩
  rw [he]
  have hh := mul_lt_mul_of_pos_left ht (mul_pos (by norm_num : (0 : ℝ)<2) htpos)
  have hc : (2*t)*(c/(2*t^2))=c/t := by field_simp [ht0.ne'] <;> ring
  simpa only [hc] using hh

end OperatorDerivativeRewrite.Foundation.FourCubeHessianMeanValue
