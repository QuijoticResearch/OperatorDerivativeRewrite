import Foundation.IBMSpatialCompletedTestLimit

/-! Exact realized domain and actual Lebesgue-kernel identities on the
completed spatial test space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialCompletedKernelIdentity
open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation
open IBMSpatialBoundedTestOperator IBMSpatialLipschitzTestLimit IBMSpatialCompletedTestLimit
open IBMSpatialKernelTesting IBMSpatialIncrementKernel IBMUniformClockGridEnergy IBMSpatialClockEnergy

theorem realized_range : LinearMap.range realize.toLinearMap = lipschitzTests.topologicalClosure := by
  have hc : IsClosed (LinearMap.range realize.toLinearMap : Set Tests) :=
    realize.isometry.isClosedEmbedding.isClosed_range
  apply le_antisymm
  · rintro F ⟨z,rfl⟩
    refine UniformSpace.Completion.induction_on z ?_ ?_
    · exact lipschitzTests.isClosed_topologicalClosure.preimage realize.continuous
    · intro G
      change realize (G:Completed) ∈ lipschitzTests.topologicalClosure
      rw [realize_coe]
      exact lipschitzTests.le_topologicalClosure G.property
  · apply Submodule.topologicalClosure_minimal
    · intro F hF
      exact ⟨(⟨F,hF⟩ : Core),realize_coe ⟨F,hF⟩⟩
    · exact hc

private theorem time_grid (T : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    uniformTime T N i = grid (T/(N+1)) i.val := by
  unfold uniformTime grid
  push_cast
  ring

theorem finiteValue_kernel (F : Tests) (T : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    finiteValue F T N Y = ∫ z, kernel (radius (T/(N+1)) Y) (N+1) z*F z ∂(volume.prod volume) := by
  unfold finiteValue
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    cellPair F |process (grid (T/(N+1)) i) Y| |process (grid (T/(N+1)) (i+1)) Y|) (N+1)]
  have he : (fun z => kernel (radius (T/(N+1)) Y) (N+1) z*F z) =
      fun z => ∑ i ∈ Finset.range (N+1), rectangle (interval (radius (T/(N+1)) Y) i) z*F z := by
    funext z
    simp only [kernel,Finset.sum_mul]
  have hi (i : ℕ) : Integrable (fun z => rectangle (interval (radius (T/(N+1)) Y) i) z*F z) (volume.prod volume) := by
    change Integrable (fun z => rectangle (cellSet (radius (T/(N+1)) Y i) (radius (T/(N+1)) Y (i+1))) z*F z) (volume.prod volume)
    exact cell_pair_integrable F F.continuous.measurable ‖F‖ F.norm_coe_le_norm _ _
  rw [he,integral_finsetSum _ (fun i _ => hi i)]
  rfl

theorem completed_kernel_actual (T : ℝ≥0) (N : ℕ) (z : Completed) :
    IBMSpatialCompletedTestLimit.finiteOperator T N z =ᵐ[gaussianProduct] fun Y =>
      ∫ a, kernel (radius (T/(N+1)) Y) (N+1) a*realize z a ∂(volume.prod volume) :=
  (finite_actual T N z).trans (ae_of_all _ fun Y => finiteValue_kernel (realize z) T N Y)

theorem completed_kernel_memLp (T : ℝ≥0) (N : ℕ) (z : Completed) :
    MemLp (fun Y => ∫ a, kernel (radius (T/(N+1)) Y) (N+1) a*realize z a ∂(volume.prod volume))
      1 gaussianProduct :=
  (Lp.memLp (IBMSpatialCompletedTestLimit.finiteOperator T N z)).ae_eq (completed_kernel_actual T N z)

theorem completed_kernel_absolute_mean_bound (T : ℝ≥0) (N : ℕ) (z : Completed) :
    (∫ Y, |∫ a, kernel (radius (T/(N+1)) Y) (N+1) a*realize z a ∂(volume.prod volume)| ∂gaussianProduct) ≤
      (T:ℝ)*‖z‖ := by
  have hb := finite_bound T N z
  rw [L1.norm_eq_integral_norm] at hb
  apply le_trans ?_ hb
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [completed_kernel_actual T N z] with Y hY
  rw [hY,Real.norm_eq_abs]

end OperatorDerivativeRewrite.Foundation.IBMSpatialCompletedKernelIdentity
