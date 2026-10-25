import Foundation.IBMSpatialKernelConcentration

/-! Exact transport of the finite spatial kernel to the ORIGINAL IBM source
energy. Its concentrating mass is the actual folded-clock quadratic variation. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialClockEnergy
open InfiniteGaussian IBMPhysicalNoiseRealization IBMPhysicalNoiseVectors
open IBMRawGridSecondChaos IBMRawStepSources IBMUniformClockGridEnergy
open IBMRawGridObservableTests IBMSpatialIncrementKernel IBMSpatialKernelConcentration

def radius (h : ℝ≥0) (Y : SampleSpace) (i : ℕ) : ℝ := |GaussianTimeProcess.process (grid h i) Y|

theorem direction_physical (r : ℝ) :
    IBMSineSourceField.direction r = physicalToCoefficient (vector r) := by
  apply firstChaosEmbedding.injective
  rw [physicalToCoefficient_vector,IBMFullSchwartzTerminal.base_embedding]
  rfl

theorem clock_increment_physical (h : ℝ≥0) (Y : SampleSpace) (i : ℕ) :
    increment (clockCurve h Y) i = physicalToCoefficient
      (vector (radius h Y (i+1))-vector (radius h Y i)) := by
  simp only [increment,clockCurve,clockDirection,radius,map_sub,direction_physical]

theorem actual_kernel_energy (h : ℝ≥0) (n : ℕ) (Y : SampleSpace) :
    (∫ z, (kernel (radius h Y) n z)^2 ∂(volume.prod volume)) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
        (inner ℝ (increment (clockCurve h Y) i) (increment (clockCurve h Y) j))^2 := by
  rw [kernel_sq_eq_physical_gram]
  simp only [clock_increment_physical,physicalToCoefficient.inner_map_map]

theorem kernel_energy_le_source (h : ℝ≥0) (n : ℕ) (Y : SampleSpace)
    (h0 : clockCurve h Y 0 = 0) :
    (∫ z, (kernel (radius h Y) n z)^2 ∂(volume.prod volume)) ≤
      2*‖sourceSum (clockCurve h Y) n‖^2+2*clockSquares h n Y := by
  have hcap : (∑ i ∈ Finset.range n,
      (inner ℝ (clockCurve h Y n) (increment (clockCurve h Y) i))^2) ≤ clockSquares h n Y := by
    apply Finset.sum_le_sum
    intro i hi
    rw [real_inner_comm]
    simp only [increment,clockCurve,inner_sub_left,direction_overlap]
    exact overlap_increment_bound _ _ _ _
  have he := source_energy_endpoint (clockCurve h Y) n h0
  rw [actual_kernel_energy]
  nlinarith [pow_nonneg (norm_nonneg (clockCurve h Y n)) 4]

theorem concentration_source_bound (h : ℝ≥0) (n : ℕ) (Y : SampleSpace)
    (h0 : clockCurve h Y 0 = 0) {M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hr : ∀ i ≤ n, radius h Y i ≤ M)
    (hm : ∀ i < n, |radius h Y (i+1)-radius h Y i| ≤ δ) :
    (∑ i ∈ Finset.range n, (radius h Y (i+1)-radius h Y i)^2)^2 ≤
      (4*M*δ)*(‖sourceSum (clockCurve h Y) n‖^2+clockSquares h n Y) := by
  have hc := kernel_concentration_bound (radius h Y) n hM hδ
    (fun i hi => ⟨abs_nonneg _,hr i hi⟩) hm
  rw [← kernel_sq_integral] at hc
  have he := mul_le_mul_of_nonneg_left (kernel_energy_le_source h n Y h0)
    (show 0 ≤ 2*M*δ by positivity)
  nlinarith [hc,he]

private theorem time_grid (H : ℝ≥0) (N : ℕ) (i : Fin (N+2)) :
    GaussianBrownianQuadraticVariation.uniformTime H N i = grid (H/(N+1)) i.val := by
  unfold GaussianBrownianQuadraticVariation.uniformTime grid
  push_cast
  ring

theorem uniform_mass (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) :
    (∑ i ∈ Finset.range (N+1),
      (radius (H/(N+1)) Y (i+1)-radius (H/(N+1)) Y i)^2) =
        IBMFoldedClockQuadraticVariation.foldedSum H N Y := by
  unfold IBMFoldedClockQuadraticVariation.foldedSum radius
  simp only [time_grid,Fin.val_succ,Fin.val_castSucc]
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (|GaussianTimeProcess.process (grid (H/(N+1)) (i+1)) Y|-
      |GaussianTimeProcess.process (grid (H/(N+1)) i) Y|)^2) (N+1)).symm

end OperatorDerivativeRewrite.Foundation.IBMSpatialClockEnergy
