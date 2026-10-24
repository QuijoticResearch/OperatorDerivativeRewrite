import Foundation.IBMSpatialIntegralFourth
import Foundation.IBMSpatialPointClockObstruction

/-! Exact fourth moments for the ACTUAL scenery realization of a random
spatial L2 kernel, then a bound for the genuine mollified clock integral. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialJointFourth
open InfiniteGaussian GaussianTimeHilbert IBMSpatialPointClockObstruction
open IBMPhysicalNoiseRealization

private theorem abs_four (x : ℝ) : |x|^4 = x^4 := by
  calc
    _ = (|x|^2)^2 := by ring
    _ = (x^2)^2 := by rw [sq_abs]
    _ = _ := by ring

theorem noise_memLp_four (u : TimeHilbert) : MemLp (physicalNoise u) 4 gaussianProduct := by
  change MemLp (firstChaosEmbedding (physicalToCoefficient u)) 4 gaussianProduct
  exact (firstChaos_hasGaussianLaw _).memLp (by norm_num)

theorem noise_fourth (u : TimeHilbert) :
    (∫ X, (physicalNoise u X)^4 ∂gaussianProduct) = 3*‖u‖^4 := by
  change (∫ X, (firstChaosEmbedding (physicalToCoefficient u) X)^4 ∂gaussianProduct) = _
  rw [IBMSourceMoments.firstChaos_fourth, physicalToCoefficient.norm_map]
  ring

theorem realize_fourth (U : Lp TimeHilbert 2 gaussianProduct) (hU : MemLp U 4 gaussianProduct) :
    Integrable (fun w => (realize U w)^4) IBMSourceLaws.jointMeasure ∧
      (∫ w, (realize U w)^4 ∂IBMSourceLaws.jointMeasure) =
        3*(∫ Y, ‖U Y‖^4 ∂gaussianProduct) := by
  have hs := realize_sections U
  have hi : ∀ᵐ Y ∂gaussianProduct, Integrable (fun X => (realize U (X,Y))^4) gaussianProduct := by
    filter_upwards [hs] with Y hy
    have hn := (noise_memLp_four (U Y)).integrable_norm_pow'
    apply hn.congr
    filter_upwards [hy] with X hx
    rw [hx, Real.norm_eq_abs]
    exact abs_four (physicalNoise (U Y) X)
  have he : (fun Y => ∫ X, (realize U (X,Y))^4 ∂gaussianProduct) =ᵐ[gaussianProduct]
      fun Y => 3*‖U Y‖^4 := by
    filter_upwards [hs] with Y hy
    have he : (∫ X, (realize U (X,Y))^4 ∂gaussianProduct) =
        ∫ X, (physicalNoise (U Y) X)^4 ∂gaussianProduct :=
      integral_congr_ae (hy.mono (fun X hx => congrArg (fun x => x^4) hx))
    exact he.trans (noise_fourth (U Y))
  have hn : (fun Y => ∫ X, ‖(realize U (X,Y))^4‖ ∂gaussianProduct) =ᵐ[gaussianProduct]
      fun Y => 3*‖U Y‖^4 := by
    convert he using 1
    funext Y
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun X => Real.norm_of_nonneg (by positivity))
  have hm : AEStronglyMeasurable (fun w => (realize U w)^4)
      (gaussianProduct.prod gaussianProduct) :=
    (Lp.aestronglyMeasurable (realize U)).pow 4
  have hj : Integrable (fun w => (realize U w)^4) (gaussianProduct.prod gaussianProduct) :=
    (integrable_prod_iff' hm).mpr ⟨hi, (hU.integrable_norm_pow'.const_mul 3).congr hn.symm⟩
  refine ⟨hj, ?_⟩
  change (∫ w, (realize U w)^4 ∂gaussianProduct.prod gaussianProduct) = _
  rw [integral_prod_symm _ hj, integral_congr_ae he, integral_const_mul]

theorem realize_memLp_four (U : Lp TimeHilbert 2 gaussianProduct) (hU : MemLp U 4 gaussianProduct) :
    MemLp (realize U) 4 IBMSourceLaws.jointMeasure := by
  have hi : Integrable (fun w => ‖realize U w‖^4) IBMSourceLaws.jointMeasure := by
    apply (realize_fourth U hU).1.congr
    exact Filter.Eventually.of_forall (fun w => by
      change (realize U w)^4 = ‖realize U w‖^4
      rw [Real.norm_eq_abs, abs_four])
  apply (integrable_norm_rpow_iff (Lp.aestronglyMeasurable _)
    (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)).mp
  simpa using hi

theorem integral_joint_fourth (r : ℕ) (T : ℝ≥0) :
    Integrable (fun w => (realize (IBMSpatialPointClockEnergy.integralValue r T) w)^4)
      IBMSourceLaws.jointMeasure ∧
      (∫ w, (realize (IBMSpatialPointClockEnergy.integralValue r T) w)^4
        ∂IBMSourceLaws.jointMeasure) ≤ 9*(T : ℝ)^2*‖IBMPhysicalWhiteNoiseObstruction.profile r‖^4 := by
  have h := realize_fourth (IBMSpatialPointClockEnergy.integralValue r T)
    (IBMSpatialIntegralFourth.integral_memLp_four r T)
  refine ⟨h.1, ?_⟩
  rw [h.2]
  nlinarith [(IBMSpatialIntegralFourth.integral_fourth r T).2]

end OperatorDerivativeRewrite.Foundation.IBMSpatialJointFourth
