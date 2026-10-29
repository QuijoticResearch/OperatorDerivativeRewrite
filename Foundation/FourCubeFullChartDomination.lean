import Foundation.FourCubeFullChartOdd

/-! Source-uniform Gaussian cutoff control on the actual full32 Haar chart.
This is unnormalized pointwise domination, not a normalized Haar limit. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullChartDomination
open QuaternionSU2Representation OneSidedBlockRank
open SU2GaussianConeCoordinates SU2HemisphereChart FourCubeFullChartOdd

attribute [local irreducible] OneSidedBlockIncidence.edges

def mass (Y : Coordinates) : ℝ := ∑ e : Interior,(chartRate (Y e)-1)

theorem mass_nonneg (Y : Coordinates) : 0 ≤ mass Y := by
  unfold mass
  apply Finset.sum_nonneg
  intro e he
  exact sub_nonneg.mpr (FourCubeHemisphereCoercivity.chartRate_ge_one (Y e))

theorem mass_smul (t : ℝ) (Y : Coordinates) : mass (t • Y)=t^2*mass Y := by
  unfold mass
  simp only [Pi.smul_apply,FourCubeHemisphereCoercivity.chartRate_smul,Finset.mul_sum]

/-- All32 links, arbitrary boundary sources, with no pinned coordinate. -/
theorem local_completed_lower (b : Fin 3 → SU2) (Y : Coordinates)
    (hY : ∀ e,chartRate (Y e) ≤ 2) :
    mass Y/4 ≤ FourCubeCompletedHaar.completedAction b (state Y 1) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun e _ => FourCubeHemisphereCoercivity.local_defect_lower (Y e) (hY e))
  rw [← Finset.sum_div] at hs
  change mass Y/4 ≤ _ at hs
  have hc := FourCubeCompletedHaar.completed_coercivity b (state Y 1)
  simpa only [state,one_smul] using hs.trans (by simpa only [state,one_smul] using hc)

theorem scaled_completed_lower (b : Fin 3 → SU2) (β t : ℝ)
    (hβ : 0 ≤ β) (ht : β*t^2=1) (Y : Coordinates)
    (hY : ∀ e,chartRate (t • Y e) ≤ 2) :
    mass Y/4 ≤ β*FourCubeCompletedHaar.completedAction b (state Y t) := by
  have h := mul_le_mul_of_nonneg_left (local_completed_lower b (t • Y) hY) hβ
  rw [mass_smul] at h
  have he : β*(t^2*mass Y/4)=mass Y/4 := by
    calc
      _ = (β*t^2)*mass Y/4 := by ring
      _ = _ := by rw [ht,one_mul]
  rw [he] at h
  have hh : state (t • Y) 1=state Y t := by
    funext e
    simp only [state,Pi.smul_apply,one_smul]
  rw [hh] at h
  exact h

theorem completed_weight_bound (b : Fin 3 → SU2) (β t : ℝ)
    (hβ : 0 ≤ β) (ht : β*t^2=1) (Y : Coordinates)
    (hY : ∀ e,chartRate (t • Y e) ≤ 2) :
    FourCubeCompletedHaar.completedWeight β b (state Y t) ≤ Real.exp (-mass Y/4) := by
  apply Real.exp_le_exp.mpr
  have h := scaled_completed_lower b β t hβ ht Y hY
  change -β*FourCubeCompletedHaar.completedAction b (state Y t) ≤ -mass Y/4
  linarith

end OperatorDerivativeRewrite.Foundation.FourCubeFullChartDomination
