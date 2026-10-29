import Foundation.FourCubeCubicIntegral
import Mathlib.Analysis.Calculus.DSlope

/-! Actual full-Haar odd free-energy correction, with a proved positive logarithmic limit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeCubicFreeEnergy
open FourCubeCubicIntegral FourCubeMovingSchurLimit FourCubeScaledBoundaryControl
open FourCubePinnedHaar FourCubePinnedConcentration

private theorem log_odd_limit (f g : ℝ → ℝ) (R L : ℝ) (hR : 0 < R)
    (hfpos : ∀ t,0 < f t) (hgpos : ∀ t,0 < g t)
    (hf : Tendsto f (𝓝[≠] 0) (𝓝 R))
    (ho : Tendsto (fun t : ℝ => (f t-g t)/(2*t)) (𝓝[≠] 0) (𝓝 L)) :
    Tendsto (fun t : ℝ => (Real.log (f t)-Real.log (g t))/(2*t)) (𝓝[≠] 0) (𝓝 (L/R)) := by
  let O := fun t : ℝ => (f t-g t)/(2*t)
  let D := fun t : ℝ => (f t-g t)/g t
  let F := fun u : ℝ => Real.log (1+u)
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hh := hf.sub ((ht.const_mul 2).mul ho)
  simp only [mul_zero,zero_mul,sub_zero] at hh
  have hg : Tendsto g (𝓝[≠] 0) (𝓝 R) := by
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t htn
    field_simp [show t ≠ 0 from htn]
    ring
  have hd : Tendsto D (𝓝[≠] 0) (𝓝 0) := by
    convert! (hf.sub hg).div hg hR.ne' using 1 <;> simp [D,Pi.div_apply]
  have hF : HasDerivAt F 1 0 := by
    convert! (Real.hasDerivAt_log (x := 1+(0 : ℝ)) (by norm_num)).comp 0
      ((hasDerivAt_id (0 : ℝ)).const_add 1) using 1 <;> norm_num [F]
  have hs : Tendsto (fun t => dslope F 0 (D t)) (𝓝[≠] 0) (𝓝 1) := by
    have hc := (continuousAt_dslope_same.mpr hF.differentiableAt).tendsto.comp hd
    convert! hc using 1 <;> simp [dslope_same,hF.deriv,Function.comp_def]
  have hlim := (hs.mul ho).div hg hR.ne'
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t htn
  have htn' : t ≠ 0 := htn
  have hdval : 1+D t=f t/g t := by
    dsimp [D]
    field_simp [(hgpos t).ne']
    ring
  have hdif := sub_smul_dslope F 0 (D t)
  simp only [sub_zero,smul_eq_mul,F,add_zero,Real.log_one] at hdif
  have hlogs : D t*dslope F 0 (D t)=Real.log (f t)-Real.log (g t) := by
    rw [hdif,hdval,Real.log_div (hfpos t).ne' (hgpos t).ne']
  change (dslope F 0 (D t)*O t)/g t=(Real.log (f t)-Real.log (g t))/(2*t)
  calc
    _ = (D t*dslope F 0 (D t))/(2*t) := by
      dsimp [D,O]
      field_simp [htn',(hgpos t).ne'] <;> ring
    _ = _ := by rw [hlogs]

theorem normalizedPartition_positive (t x y z : ℝ) :
    0 < normalizedPartition (1/t^2) (movingBoundary t x y z) :=
  div_pos (pinnedPartition_positive _ _) (normalizer_positive _)

theorem actual_freeEnergy_harmonic_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (-Real.log (normalizedPartition (1/t^2) (movingBoundary t x y z))+
      Real.log (normalizedPartition (1/t^2) (movingBoundary (-t) x y z)))/(2*t)) (𝓝[≠] 0)
      (𝓝 (harmonicCubic x y z)) := by
  let R := Real.exp (-effectiveEnergy x y z/2)
  have hh := log_odd_limit
    (fun t => normalizedPartition (1/t^2) (movingBoundary t x y z))
    (fun t => normalizedPartition (1/t^2) (movingBoundary (-t) x y z))
    R (-harmonicCubic x y z*R) (Real.exp_pos _)
    (fun t => normalizedPartition_positive t x y z)
    (fun t => by simpa only [neg_sq] using normalizedPartition_positive (-t) x y z)
    (moving_partition_ratio_schur x y z) (actual_normalized_partition_harmonic_odd_limit x y z)
  rw [mul_div_cancel_right₀ _ (Real.exp_pos _).ne'] at hh
  have hn := hh.neg
  simp only [neg_neg] at hn
  apply hn.congr'
  filter_upwards with t
  ring

end OperatorDerivativeRewrite.Foundation.FourCubeCubicFreeEnergy
