import Foundation.FourCubeFullHaarOddFreeEnergy
import Foundation.YMBlockHeatContractionObstruction

/-! A conditional comparison-error obstruction for the actual full32 boundary response.
The error must control BOTH scalar free-energy discrepancies; no operator norm
is silently asserted to do so. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeActualErrorBudget
open FourCubeFullHaarGaussianLimit FourCubeFullHaarOddFreeEnergy
open YMBlockHeatContractionObstruction

def rayFreeEnergy (x y z t : ℝ) : ℝ :=
  FourCubeCompletedHaar.standardFreeEnergy (1/t^2) (parameters x y z t)
def coefficient (x y z : ℝ) : ℝ := ((1784975 : ℝ)/2750517)*x*y*z

theorem ray_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (rayFreeEnergy x y z t-rayFreeEnergy x y z (-t))/(2*t))
      (𝓝[≠] 0) (𝓝 (coefficient x y z)) := by
  simpa only [rayFreeEnergy,neg_sq,coefficient] using standard_free_energy_odd_limit x y z

theorem paired_error_lower (x y z : ℝ) (hxyz : 0 < x*y*z)
    (reference error : ℝ → ℝ)
    (herrors : ∀ᶠ t : ℝ in 𝓝[>] 0,
      |rayFreeEnergy x y z t-reference t| ≤ error t ∧
        |rayFreeEnergy x y z (-t)-reference t| ≤ error t) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,coefficient x y z*t/2 < error t := by
  have hc : 0 < coefficient x y z := by
    unfold coefficient
    simpa only [mul_assoc] using
      mul_pos (show (0 : ℝ) < (1784975 : ℝ)/2750517 by norm_num) hxyz
  have hf : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun t ht => ne_of_gt ht)
  have hq := ((ray_odd_limit x y z).mono_left hf).eventually
    (eventually_gt_nhds (show coefficient x y z/2 < coefficient x y z by linarith))
  filter_upwards [herrors,hq,self_mem_nhdsWithin] with t he hquot ht
  have hden : 0 < 2*t := mul_pos (by norm_num) ht
  have hdiff := (lt_div_iff₀ hden).mp hquot
  have hb : rayFreeEnergy x y z t-rayFreeEnergy x y z (-t) ≤ 2*error t := by
    have ha := abs_sub_le (rayFreeEnergy x y z t) (reference t) (rayFreeEnergy x y z (-t))
    rw [abs_sub_comm (reference t)] at ha
    linarith [le_abs_self (rayFreeEnergy x y z t-rayFreeEnergy x y z (-t)),he.1,he.2]
  nlinarith

/-- Incompatibility is conditional on the SAME allowance controlling both free energies. -/
theorem no_common_reference_contraction (x y z gap curvatureScale : ℝ)
    (hxyz : 0 < x*y*z) (reference error : ℝ → ℝ) :
    ¬ (∀ᶠ t : ℝ in 𝓝[>] 0,
      |rayFreeEnergy x y z t-reference t| ≤ error t ∧
      |rayFreeEnergy x y z (-t)-reference t| ≤ error t ∧
        referenceFactor gap curvatureScale (1/t^2)+error t < 1) := by
  intro h
  have he := paired_error_lower x y z hxyz reference error
    (h.mono (fun t ht => ⟨ht.1,ht.2.1⟩))
  have hc : 0 < coefficient x y z := by
    unfold coefficient
    simpa only [mul_assoc] using
      mul_pos (show (0 : ℝ) < (1784975 : ℝ)/2750517 by norm_num) hxyz
  have hs : ∀ᶠ t : ℝ in 𝓝[>] 0,
      2*(gap/curvatureScale)*t < coefficient x y z := by
    have hl : Tendsto (fun t : ℝ => 2*(gap/curvatureScale)*t) (𝓝[>] 0) (𝓝 0) := by
      simpa only [mul_zero,id_eq] using
        (tendsto_id.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).const_mul (2*(gap/curvatureScale))
    exact hl.eventually (eventually_lt_nhds hc)
  obtain ⟨t,hh,hel,hsmall,ht⟩ := (h.and (he.and (hs.and self_mem_nhdsWithin))).exists
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hb := necessary_error_budget gap curvatureScale (1/t^2) (error t) hh.2.2
  have hid : gap/(curvatureScale*(1/t^2))=(gap/curvatureScale)*t^2 := by
    field_simp [ht0]
  rw [hid] at hb
  have hsm := mul_lt_mul_of_pos_right hsmall ht
  nlinarith

end OperatorDerivativeRewrite.Foundation.FourCubeActualErrorBudget
