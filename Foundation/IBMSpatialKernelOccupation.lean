import Foundation.IBMSpatialClockKernelError

/-! Actual finite spatial increment-square kernels converge when tested by
bounded Lipschitz functions to the original clock diagonal occupation. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialKernelOccupation
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMSpatialKernelTesting IBMSpatialIncrementKernel IBMClippedClockStrongLimit
open IBMUniformClockGridEnergy IBMSpatialClockEnergy

def diagonal (F : ℝ × ℝ → ℝ) (x : ℝ) : ℝ := F (|x|,|x|)

theorem diagonal_lipschitz (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F) :
    LipschitzWith K (diagonal F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ (K:ℝ)*dist (|x|,|x|) (|y|,|y|) := hF.dist_le_mul _ _
    _ ≤ _ := by
      simp only [Prod.dist_eq,max_self,Real.dist_eq]
      exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub x y) K.coe_nonneg

def action (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (N : ℕ) : Lp ℝ 1 gaussianProduct :=
  clockL1 (IBMSpatialClockKernelError.errorSum F hF C hC T N)+
    IBMClockWeightedFoldedVariation.folded (diagonal F) (diagonal_lipschitz F hF) C
      (fun x => hC (|x|,|x|)) T N

def occupation (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F) (T : ℝ≥0) : Lp ℝ 1 gaussianProduct :=
  clockL1 (IBMClockWeightedFoldedVariation.drift (diagonal F) (diagonal_lipschitz F hF) T)

theorem action_actual (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    action F hF C hC T N =ᵐ[gaussianProduct] fun Y => ∑ i : Fin (N+1),
      cellPair F |process (uniformTime T N i.castSucc) Y| |process (uniformTime T N i.succ) Y| := by
  let E := IBMSpatialClockKernelError.errorSum F hF C hC T N
  let Q := IBMClockWeightedFoldedVariation.folded (diagonal F) (diagonal_lipschitz F hF) C
    (fun x => hC (|x|,|x|)) T N
  filter_upwards [Lp.coeFn_add (clockL1 E) Q,clockL1_actual E,
    IBMSpatialClockKernelError.errorSum_actual F hF C hC T N,
    IBMClockWeightedFoldedVariation.folded_actual (diagonal F) (diagonal_lipschitz F hF) C
      (fun x => hC (|x|,|x|)) T N] with Y ha hl he hq
  change action F hF C hC T N Y = _ at ha
  rw [ha,Pi.add_apply,hl,he,hq,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by unfold IBMSpatialClockKernelError.error diagonal; ring

private theorem time_grid (T : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime T N i = grid (T/(N+1)) i.val := by
  unfold uniformTime grid
  push_cast
  ring

theorem action_actual_kernel (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    action F hF C hC T N =ᵐ[gaussianProduct] fun Y =>
      ∫ z, kernel (radius (T/(N+1)) Y) (N+1) z*F z ∂(volume.prod volume) := by
  filter_upwards [action_actual F hF C hC T N] with Y ha
  rw [ha]
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    cellPair F |process (grid (T/(N+1)) i) Y| |process (grid (T/(N+1)) (i+1)) Y|) (N+1)]
  have he : (fun z => kernel (radius (T/(N+1)) Y) (N+1) z*F z) =
      fun z => ∑ i ∈ Finset.range (N+1),
        rectangle (interval (radius (T/(N+1)) Y) i) z*F z := by
    funext z
    simp only [kernel,Finset.sum_mul]
  have hi (i : ℕ) : Integrable (fun z => rectangle (interval (radius (T/(N+1)) Y) i) z*F z) (volume.prod volume) := by
    change Integrable (fun z => rectangle (cellSet (radius (T/(N+1)) Y i) (radius (T/(N+1)) Y (i+1))) z*F z) (volume.prod volume)
    exact cell_pair_integrable F hF.continuous.measurable C hC _ _
  rw [he,integral_finsetSum _ (fun i _ => hi i)]
  rfl

theorem action_tendsto (F : ℝ × ℝ → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F)
    (C : ℝ) (hC : ∀ z, ‖F z‖ ≤ C) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (action F hF C hC T) atTop (𝓝 (occupation F hF T)) := by
  have hz : clockL1 (0:GaussianL2) = 0 := by
    apply Lp.ext
    filter_upwards [clockL1_actual (0:GaussianL2),Lp.coeFn_zero ℝ 2 gaussianProduct,
      Lp.coeFn_zero ℝ 1 gaussianProduct] with Y hl h2 h1
    exact hl.trans (h2.trans h1.symm)
  have h := (clockL1_tendsto _ _ (IBMSpatialClockKernelError.errorSum_tendsto F hF C hC T)).add
    (IBMClockWeightedFoldedVariation.folded_tendsto (diagonal F) (diagonal_lipschitz F hF) C
      (fun x => hC (|x|,|x|)) T hT)
  unfold action occupation
  simpa only [hz,zero_add] using h

end OperatorDerivativeRewrite.Foundation.IBMSpatialKernelOccupation
