import Foundation.FourCubeCubicSignAverage

/-! Exact evaluation of the genuine signed cubic Haar correction by color reflections. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeCubicIntegral
open FourCubeMovingOddAction FourCubeColorReflection FourCubeCubicSignAverage
open FourCubeOddIntegral FourCubeOddFullPartition FourCubeMovingSchurLimit
open FourCubeMovingLaplaceLimit FourCubeHaarLaplaceDensity FourCubeScaledBoundaryControl

def harmonicCubic (x y z : ℝ) : ℝ := cubicCoefficient (harmonicShift x y z) x y z

theorem firstDensity_sign_sum (x y z : ℝ) (Y : Coordinates) :
    (∑ s : Signs,firstDensity x y z (affine s (harmonicShift x y z) Y))=
      (-8*harmonicCubic x y z)*limitingDensity x y z Y := by
  simp_rw [firstDensity,limitingDensity_affine]
  rw [← Finset.sum_mul,Finset.sum_neg_distrib,actual_cubic_sign_sum]
  unfold harmonicCubic
  ring

theorem firstDensity_integral_harmonic (x y z : ℝ) :
    (∫ Y : Coordinates,firstDensity x y z Y)=
      -harmonicCubic x y z*(∫ Y : Coordinates,limitingDensity x y z Y) := by
  have hi (s : Signs) : Integrable (fun Y : Coordinates =>
      firstDensity x y z (affine s (harmonicShift x y z) Y)) :=
    (affine_preserving s _).integrable_comp_of_integrable (firstDensity_integrable x y z)
  have hh : (8 : ℝ)*(∫ Y : Coordinates,firstDensity x y z Y)=
      (-8*harmonicCubic x y z)*(∫ Y : Coordinates,limitingDensity x y z Y) := by
    calc
      _ = ∑ s : Signs,∫ Y : Coordinates,firstDensity x y z (affine s (harmonicShift x y z) Y) := by
        simp only [integral_affine,Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_bool,
          nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
        ring
      _ = ∫ Y : Coordinates,∑ s : Signs,firstDensity x y z (affine s (harmonicShift x y z) Y) :=
        (integral_finsetSum Finset.univ (fun s _ => hi s)).symm
      _ = _ := by simp_rw [firstDensity_sign_sum]; rw [integral_const_mul]
  linarith

theorem firstDensity_integral_schur (x y z : ℝ) :
    (∫ Y : Coordinates,firstDensity x y z Y)=
      (-harmonicCubic x y z*Real.exp (-effectiveEnergy x y z/2))*
        (∫ Y : Coordinates,gaussianDensity Y) := by
  rw [firstDensity_integral_harmonic,limitingDensity_integral_schur]
  ring

theorem actual_full_partition_harmonic_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (FourCubePinnedHaar.pinnedPartition (1/t^2) (movingBoundary t x y z)-
      FourCubePinnedHaar.pinnedPartition (1/t^2) (movingBoundary (-t) x y z))/(2*t*|t|^93)) (𝓝[≠] 0)
      (𝓝 ((-harmonicCubic x y z*Real.exp (-effectiveEnergy x y z/2))*
        (∫ Y : Coordinates,gaussianDensity Y))) := by
  simpa only [firstDensity_integral_schur] using actual_full_partition_odd_limit x y z

theorem actual_normalized_partition_harmonic_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (normalizedPartition (1/t^2) (movingBoundary t x y z)-
      normalizedPartition (1/t^2) (movingBoundary (-t) x y z))/(2*t)) (𝓝[≠] 0)
      (𝓝 (-harmonicCubic x y z*Real.exp (-effectiveEnergy x y z/2))) := by
  have hh := actual_normalized_partition_odd_limit x y z
  rw [firstDensity_integral_schur,mul_div_cancel_right₀ _ gaussianDensity_integral_positive.ne'] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.FourCubeCubicIntegral
