import Foundation.FourCubeFullHaarGaussianLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Source-uniform off-cutoff control and actual full32 completed-Haar partition
asymptotics. No normalized-tail claim precedes the positive Gaussian normalization. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullHaarAsymptotic
open QuaternionSU2Representation OneSidedBlockRank FourCubeHaarParity FourCubePinnedCoercivity
open FourCubeFullChartOdd FourCubeFullHaarCoordinates FourCubeFullHaarCutoff
open FourCubeFullHaarGaussianLimit

attribute [local irreducible] OneSidedBlockIncidence.edges

def outsidePartition (b : Fin 3 → SU2) (β : ℝ) : ℝ :=
  ∫ U in physicalCutoffᶜ,FourCubeCompletedHaar.completedWeight β b U ∂interiorHaar

theorem outside_energy (b : Fin 3 → SU2) (U : InteriorState) (hU : U∈physicalCutoffᶜ) :
    1/4 ≤ FourCubeCompletedHaar.completedAction b U := by
  by_contra hn
  have hC : FourCubeCompletedHaar.completedAction b U<1/4 := lt_of_not_ge hn
  apply hU
  intro e
  have he := Finset.single_le_sum (fun i (_ : i∈Finset.univ) => defect_nonneg (U i))
    (Finset.mem_univ e)
  have hd : defect (U e)<1/4 :=
    (he.trans (FourCubeCompletedHaar.completed_coercivity b U)).trans_lt hC
  exact ⟨by unfold defect at hd; linarith,FourCubeHemisphereCoercivity.small_defect_chartRate (U e) hd⟩

theorem outside_nonneg (b : Fin 3 → SU2) (β : ℝ) : 0 ≤ outsidePartition b β :=
  integral_nonneg (fun U => (Real.exp_pos _).le)

/-- Uniform in every source, before dividing by any partition function. -/
theorem outside_bound (b : Fin 3 → SU2) (β : ℝ) (hβ : 0 ≤ β) :
    outsidePartition b β ≤ Real.exp (-β/4) := by
  have h := norm_setIntegral_le_of_norm_le_const
    (μ := interiorHaar) (s := physicalCutoffᶜ)
    (f := FourCubeCompletedHaar.completedWeight β b) (measure_lt_top _ _)
    (fun U hU => by
      change ‖Real.exp (-β*FourCubeCompletedHaar.completedAction b U)‖ ≤ Real.exp (-β/4)
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have he := outside_energy b U hU
      change -β*FourCubeCompletedHaar.completedAction b U ≤ -β/4
      nlinarith)
  have hm : interiorHaar.real physicalCutoffᶜ ≤ 1 := measureReal_le_one
  have hh := mul_le_mul_of_nonneg_left hm (Real.exp_pos (-β/4)).le
  simp only [mul_one] at hh
  exact (le_abs_self _).trans (h.trans hh)

theorem partition_split (b : Fin 3 → SU2) (β : ℝ) :
    FourCubeCompletedHaar.completedPartition β b=localPartition b β+outsidePartition b β :=
  (integral_add_compl physicalCutoff_measurable (FourCubeCompletedHaar.completed_integrable β b)).symm

private theorem exponential_scale_limit :
    Tendsto (fun t : ℝ => Real.exp (-(1/t^2)/4)/|t|^96) (𝓝[≠] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (48 : ℝ) (1/4) (by norm_num)).comp
    FourCubeHaarPartitionAsymptotic.inverse_square_tendsto
  simp only [Real.rpow_ofNat,Function.comp_def] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hp : |t|^(96 : ℕ)=(t^2)^(48 : ℕ) := by
    calc
      _ = (|t|^2)^48 := by rw [← pow_mul]
      _ = _ := by rw [sq_abs]
  rw [div_pow,one_pow,← hp]
  have he : -(1/4 : ℝ)*(1/t^2)=-(1/t^2)/4 := by ring
  rw [he]
  ring

theorem outside_scaled_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => outsidePartition (parameters x y z t) (1/t^2)/|t|^96)
      (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => div_nonneg (outside_nonneg _ _) (by positivity)))
    (Filter.Eventually.of_forall (fun t => div_le_div_of_nonneg_right (outside_bound _ _ (by positivity)) (by positivity)))
    exponential_scale_limit

/-- Actual unrestricted32-link completed Haar partition; positive finite leading coefficient. -/
theorem full_partition_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => FourCubeCompletedHaar.completedPartition (1/t^2) (parameters x y z t)/|t|^96)
      (𝓝[≠] 0) (𝓝 (∫ Y : Coordinates,gaussianDensity x y z Y)) := by
  have h := (actual_cutoff_partition_limit x y z).add (outside_scaled_limit x y z)
  simpa only [add_zero,← add_div,← partition_split] using h

/-- Normalized off-cutoff mass follows only AFTER the verified positive full normalization. -/
theorem normalized_outside_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => outsidePartition (parameters x y z t) (1/t^2)/
      FourCubeCompletedHaar.completedPartition (1/t^2) (parameters x y z t)) (𝓝[≠] 0) (𝓝 0) := by
  have h := (outside_scaled_limit x y z).div (full_partition_limit x y z) (gaussian_integral_positive x y z).ne'
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hz := (FourCubeCompletedHaar.completed_positive (1/t^2) (parameters x y z t)).ne'
  change (outsidePartition (parameters x y z t) (1/t^2)/|t|^96)/
    (FourCubeCompletedHaar.completedPartition (1/t^2) (parameters x y z t)/|t|^96)=
    outsidePartition (parameters x y z t) (1/t^2)/
      FourCubeCompletedHaar.completedPartition (1/t^2) (parameters x y z t)
  field_simp [hz,abs_ne_zero.mpr ht]

end OperatorDerivativeRewrite.Foundation.FourCubeFullHaarAsymptotic
