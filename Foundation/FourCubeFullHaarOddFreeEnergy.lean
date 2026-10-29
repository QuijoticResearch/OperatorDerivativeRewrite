import Foundation.FourCubeFullHaarOddAsymptotic

/-! Actual unrestricted full32 completed and standard Haar odd free-energy limits.
This finite-box boundary response supplies no physical spectral-gap assertion. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullHaarOddFreeEnergy
open FourCubeFullChartOdd FourCubeFullHaarGaussianLimit FourCubeFullHaarAsymptotic
open FourCubeFullHaarOddAsymptotic

private theorem log_odd_limit (f g : ℝ → ℝ) (R L : ℝ) (hR : 0 < R)
    (hfpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ),0 < f t)
    (hgpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ),0 < g t)
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
  filter_upwards [self_mem_nhdsWithin,hfpos,hgpos] with t htn hfpt hgpt
  have htn' : t ≠ 0 := htn
  have hdval : 1+D t=f t/g t := by
    dsimp [D]
    field_simp [hgpt.ne']
    ring
  have hdif := sub_smul_dslope F 0 (D t)
  simp only [sub_zero,smul_eq_mul,F,add_zero,Real.log_one] at hdif
  have hlogs : D t*dslope F 0 (D t)=Real.log (f t)-Real.log (g t) := by
    rw [hdif,hdval,Real.log_div hfpt.ne' hgpt.ne']
  change (dslope F 0 (D t)*O t)/g t=(Real.log (f t)-Real.log (g t))/(2*t)
  calc
    _ = (D t*dslope F 0 (D t))/(2*t) := by
      dsimp [D,O]
      field_simp [htn',hgpt.ne'] <;> ring
    _ = _ := by rw [hlogs]

/-- The actual unpinned32-link completed-Haar odd free-energy coefficient. -/
theorem completed_free_energy_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ =>
      (FourCubeCompletedHaar.completedFreeEnergy (1/t^2) (parameters x y z t)-
        FourCubeCompletedHaar.completedFreeEnergy (1/t^2) (parameters x y z (-t)))/(2*t))
      (𝓝[≠] 0) (𝓝 (((1784975 : ℝ)/2750517)*x*y*z)) := by
  let f := fun t : ℝ => FourCubeCompletedHaar.completedPartition (1/t^2)
    (parameters x y z t)/|t|^96
  let g := fun t : ℝ => FourCubeCompletedHaar.completedPartition (1/t^2)
    (parameters x y z (-t))/|t|^96
  let R := ∫ Y : Coordinates,gaussianDensity x y z Y
  let c := ((1784975 : ℝ)/2750517)*x*y*z
  have hR : 0 < R := gaussian_integral_positive x y z
  have hfpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ),0 < f t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact div_pos (FourCubeCompletedHaar.completed_positive _ _)
      (pow_pos (abs_pos.mpr ht) _)
  have hgpos : ∀ᶠ t in 𝓝[≠] (0 : ℝ),0 < g t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact div_pos (FourCubeCompletedHaar.completed_positive _ _)
      (pow_pos (abs_pos.mpr ht) _)
  have ho : Tendsto (fun t : ℝ => (f t-g t)/(2*t)) (𝓝[≠] 0) (𝓝 (-c*R)) := by
    apply (full_partition_odd_limit x y z).congr'
    filter_upwards with t
    dsimp [f,g]
    ring
  have hh := log_odd_limit f g R (-c*R) hR hfpos hgpos (full_partition_limit x y z) ho
  rw [mul_div_cancel_right₀ _ hR.ne'] at hh
  have hn := hh.neg
  simp only [neg_neg] at hn
  apply hn.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hscale : |t|^96 ≠ 0 := pow_ne_zero _ (abs_ne_zero.mpr ht)
  have hp := (FourCubeCompletedHaar.completed_positive (1/t^2) (parameters x y z t)).ne'
  have hm := (FourCubeCompletedHaar.completed_positive (1/t^2) (parameters x y z (-t))).ne'
  dsimp [f,g]
  rw [Real.log_div hp hscale,Real.log_div hm hscale]
  unfold FourCubeCompletedHaar.completedFreeEnergy
  ring

/-- Exact even source-cost cancellation transfers the limit to the full864-face action. -/
theorem standard_free_energy_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ =>
      (FourCubeCompletedHaar.standardFreeEnergy (1/t^2) (parameters x y z t)-
        FourCubeCompletedHaar.standardFreeEnergy (1/t^2) (parameters x y z (-t)))/(2*t))
      (𝓝[≠] 0) (𝓝 (((1784975 : ℝ)/2750517)*x*y*z)) := by
  apply (completed_free_energy_odd_limit x y z).congr'
  filter_upwards with t
  have he := FourCubeCompletedHaar.odd_free_energy (1/t^2) (t*x) (t*y) (t*z)
  simpa only [parameters,neg_mul] using congrArg (fun v : ℝ => v/(2*t)) he.symm

/-- Concrete nonlinear boundary ordering at sufficiently small positive scale. -/
theorem standard_free_energy_eventually_gt (x y z : ℝ) (hxyz : 0 < x*y*z) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      FourCubeCompletedHaar.standardFreeEnergy (1/t^2) (parameters x y z (-t)) <
        FourCubeCompletedHaar.standardFreeEnergy (1/t^2) (parameters x y z t) := by
  have hc : 0 < ((1784975 : ℝ)/2750517)*x*y*z := by
    simpa only [mul_assoc] using
      mul_pos (show (0 : ℝ) < (1784975 : ℝ)/2750517 by norm_num) hxyz
  have hf : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
  have h := ((standard_free_energy_odd_limit x y z).mono_left hf).eventually
    (eventually_gt_nhds hc)
  filter_upwards [h,self_mem_nhdsWithin] with t hq ht
  have hden : 0 < 2*t := mul_pos (by norm_num) ht
  exact sub_pos.mp ((div_pos_iff_of_pos_right hden).mp hq)

/-- The corresponding strict ordering concerns actual full864-face Haar partitions. -/
theorem standard_partition_eventually_lt (x y z : ℝ) (hxyz : 0 < x*y*z) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      FourCubeCompletedHaar.standardPartition (1/t^2) (parameters x y z t) <
        FourCubeCompletedHaar.standardPartition (1/t^2) (parameters x y z (-t)) := by
  filter_upwards [standard_free_energy_eventually_gt x y z hxyz] with t ht
  change -Real.log (FourCubeCompletedHaar.standardPartition (1/t^2) (parameters x y z (-t))) <
    -Real.log (FourCubeCompletedHaar.standardPartition (1/t^2) (parameters x y z t)) at ht
  apply (Real.log_lt_log_iff (FourCubeCompletedHaar.standard_positive _ _)
    (FourCubeCompletedHaar.standard_positive _ _)).mp
  linarith

end OperatorDerivativeRewrite.Foundation.FourCubeFullHaarOddFreeEnergy
