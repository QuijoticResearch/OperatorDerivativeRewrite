import Foundation.FourCubeBoundarySmoothPartition
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Repeated mean value for the actual smooth boundary free energy. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourCubeMixedMeanValue
open FourCubeHaarContinuousIntegral FourCubeBoundarySmoothPartition
open FourCubeThermalMixedDifference

def basis (j : Fin 3) : Parameters := Pi.single j 1

def spatialPartial (j : Fin 3) (F : Parameters → ℝ) (a : Parameters) : ℝ :=
  fderiv ℝ F a (basis j)

theorem partial_contDiff (j : Fin 3) (F : Parameters → ℝ) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (spatialPartial j F) :=
  (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem slice_x (F : Parameters → ℝ) (hF : ContDiff ℝ ∞ F) (x y z : ℝ) :
    HasDerivAt (fun u => F ![u,y,z]) (spatialPartial 0 F ![x,y,z]) x := by
  have hl : HasDerivAt (fun u : ℝ => (![u,y,z] : Parameters)) (basis 0) x := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert! (hasDerivAt_id x) using 1 <;> simp [basis,Pi.single_apply]
    · simpa [basis,Pi.single_apply] using hasDerivAt_const x y
    · simpa [basis,Pi.single_apply] using hasDerivAt_const x z
  exact (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt x hl

theorem slice_y (F : Parameters → ℝ) (hF : ContDiff ℝ ∞ F) (x y z : ℝ) :
    HasDerivAt (fun u => F ![x,u,z]) (spatialPartial 1 F ![x,y,z]) y := by
  have hl : HasDerivAt (fun u : ℝ => (![x,u,z] : Parameters)) (basis 1) y := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [basis,Pi.single_apply] using hasDerivAt_const y x
    · convert! (hasDerivAt_id y) using 1 <;> simp [basis,Pi.single_apply]
    · simpa [basis,Pi.single_apply] using hasDerivAt_const y z
  exact (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt y hl

theorem slice_z (F : Parameters → ℝ) (hF : ContDiff ℝ ∞ F) (x y z : ℝ) :
    HasDerivAt (fun u => F ![x,y,u]) (spatialPartial 2 F ![x,y,z]) z := by
  have hl : HasDerivAt (fun u : ℝ => (![x,y,u] : Parameters)) (basis 2) z := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [basis,Pi.single_apply] using hasDerivAt_const z x
    · simpa [basis,Pi.single_apply] using hasDerivAt_const z y
    · convert! (hasDerivAt_id z) using 1 <;> simp [basis,Pi.single_apply]
  exact (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt z hl

private theorem mean (f df : ℝ → ℝ) (hd : ∀ x,HasDerivAt f (df x) x) (h : ℝ) (hh : 0<h) :
    ∃ x∈Ioo (-h) h, df x=(f h-f (-h))/(2*h) := by
  have hc : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hd x).continuousAt)
  have he := exists_hasDerivAt_eq_slope f df (show -h<h by linarith) hc.continuousOn (fun x _ => hd x)
  simpa only [sub_neg_eq_add,← two_mul] using he

theorem cube_mean (F : Parameters → ℝ) (hF : ContDiff ℝ ∞ F) (h : ℝ) (hh : 0<h) :
    ∃ x∈Ioo (-h) h, ∃ y∈Ioo (-h) h, ∃ z∈Ioo (-h) h,
      spatialPartial 2 (spatialPartial 1 (spatialPartial 0 F)) ![x,y,z]=
        cornerSum (fun x y z => F ![x,y,z]) h/(8*h^3) := by
  have h0 := partial_contDiff 0 F hF
  have h1 := partial_contDiff 1 (spatialPartial 0 F) h0
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
  let C := fun z => spatialPartial 1 (spatialPartial 0 F) ![x,y,z]
  let C' := fun z => spatialPartial 2 (spatialPartial 1 (spatialPartial 0 F)) ![x,y,z]
  obtain ⟨z,hz,hCz⟩ := mean C C' (fun z => slice_z _ h1 x y z) h hh
  refine ⟨x,hx,y,hy,z,hz,?_⟩
  have heC : C h-C (-h)=B' y := rfl
  have heB : B h-B (-h)=A' x := by dsimp [B,A']; ring
  have heA : A h-A (-h)=cornerSum (fun x y z => F ![x,y,z]) h := by
    dsimp [A,cornerSum]
    ring
  change spatialPartial 2 (spatialPartial 1 (spatialPartial 0 F)) ![x,y,z]=_ at hCz
  rw [heC,hBy,heB,hAx,heA] at hCz
  rw [hCz]
  field_simp [hh.ne']
  <;> ring

def mixedDerivative (β : ℝ) : Parameters → ℝ :=
  spatialPartial 2 (spatialPartial 1 (spatialPartial 0 (FourCubeBoundarySmoothPartition.freeEnergy β)))

theorem actual_cube_mean (β h : ℝ) (hh : 0<h) :
    ∃ a : Parameters,(∀ i,|a i|<h) ∧ mixedDerivative β a=difference β h := by
  obtain ⟨x,hx,y,hy,z,hz,he⟩ := cube_mean (FourCubeBoundarySmoothPartition.freeEnergy β)
    (actual_freeEnergy_contDiff β) h hh
  refine ⟨![x,y,z],?_,he⟩
  intro i
  fin_cases i
  · exact abs_lt.mpr hx
  · exact abs_lt.mpr hy
  · exact abs_lt.mpr hz

theorem actual_large_derivatives :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∃ a : Parameters,(∀ i,|a i|<t) ∧ c/(2*t^2)<mixedDerivative (1/t^2) a := by
  have hm : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 :=
    nhdsWithin_mono _ (by intro t ht; exact ne_of_gt ht)
  filter_upwards [actual_third_difference_lower.filter_mono hm,self_mem_nhdsWithin] with t ht htpos
  obtain ⟨a,ha,he⟩ := actual_cube_mean (1/t^2) t htpos
  exact ⟨a,ha,by rw [he]; exact ht⟩

end OperatorDerivativeRewrite.Foundation.FourCubeMixedMeanValue
