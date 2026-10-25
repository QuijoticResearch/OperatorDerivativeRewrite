import Foundation.IBMFiniteRidgeObservation

/-! Finite ridge quadratic kernels expand into the verified ACTUAL mixed
observation energies, retaining all off-diagonal terms. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFiniteRidgeQuadraticTesting
open InfiniteGaussian IBMTimeAveragedObservable IBMRawStepSources IBMFiniteRidgeObservation
open IBMSchwartzSourceContinuity IBMSourceProductBounds IBMRawGridMixedObservable
variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (r : ι → ℝ≥0)

theorem raw_square (Y : SampleSpace) : rawProduct (direction a r Y) (direction a r Y) =
    ∑ i, ∑ j, (a i*a j) • rawProduct (clockDirection (r i) Y) (clockDirection (r j) Y) := by
  have hl : rawProduct (direction a r Y) (direction a r Y) =
      ∑ i, a i • rawProduct (clockDirection (r i) Y) (direction a r Y) := by
    change rawBilinear (∑ i, a i • clockDirection (r i) Y) (direction a r Y) = _
    rw [map_sum]
    simp only [sum_apply,map_smul,smul_apply,rawBilinear_apply]
  rw [hl]
  apply Finset.sum_congr rfl
  intro i _
  have hr : rawProduct (clockDirection (r i) Y) (direction a r Y) =
      ∑ j, a j • rawProduct (clockDirection (r i) Y) (clockDirection (r j) Y) := by
    change rawBilinear (clockDirection (r i) Y) (∑ j, a j • clockDirection (r j) Y) = _
    rw [map_sum]
    simp only [map_smul,rawBilinear_apply]
  rw [hr,Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => smul_smul (a i) (a j) _

theorem pairing_expand (f : GaussianL2) (Y : SampleSpace) :
    inner ℝ f (rawProduct (direction a r Y) (direction a r Y)) =
      ∑ i, ∑ j, (a i*a j)*inner ℝ f
        (rawProduct (clockDirection (r i) Y) (clockDirection (r j) Y)) := by
  rw [raw_square]
  simp only [inner_sum,real_inner_smul_right]

def native (H : ℝ≥0) (N : ℕ) : GaussianL2 :=
  ∑ i, ∑ j, (a i*a j) • IBMActualQuadraticL2Reconstruction.native H (r i) (r j) N

def reconstruction (H : ℝ≥0) : GaussianL2 :=
  ∑ i, ∑ j, (a i*a j) • IBMActualQuadraticL2Reconstruction.reconstruction H (r i) (r j)

def limitValue (H : ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i, ∑ j, (a i*a j)*
    (IBMClippedClockCrossing.cap (GaussianTimeProcess.process (r i) Y)
      (GaussianTimeProcess.process H Y)*
      IBMClippedClockCrossing.cap (GaussianTimeProcess.process (r j) Y)
        (GaussianTimeProcess.process H Y)-
        IBMMixedClockLimit.mixedOccupation H (r i) (r j) Y)

theorem reconstruction_actual (H : ℝ≥0) :
    reconstruction a r H =ᵐ[gaussianProduct] limitValue a r H := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
      ∑ j, (a i*a j) • IBMActualQuadraticL2Reconstruction.reconstruction H (r i) (r j)),
    ae_all_iff.mpr (fun i => Lp.coeFn_finsetSum Finset.univ
      (fun j => (a i*a j) • IBMActualQuadraticL2Reconstruction.reconstruction H (r i) (r j))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => Lp.coeFn_smul (a i*a j)
      (IBMActualQuadraticL2Reconstruction.reconstruction H (r i) (r j)))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      IBMActualQuadraticL2Reconstruction.reconstruction_actual H (r i) (r j)))] with Y hs hi hm hv
  change reconstruction a r H Y = _ at hs
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hm i j,Pi.smul_apply,hv i j,smul_eq_mul]

theorem native_actual (H : ℝ≥0) (N : ℕ) : native a r H N =ᵐ[gaussianProduct] fun Y =>
    ∑ i, ∑ j, (a i*a j)*mixedEnergy (H/(N+1)) (N+1) (r i) (r j) Y := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
      ∑ j, (a i*a j) • IBMActualQuadraticL2Reconstruction.native H (r i) (r j) N),
    ae_all_iff.mpr (fun i => Lp.coeFn_finsetSum Finset.univ
      (fun j => (a i*a j) • IBMActualQuadraticL2Reconstruction.native H (r i) (r j) N)),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => Lp.coeFn_smul (a i*a j)
      (IBMActualQuadraticL2Reconstruction.native H (r i) (r j) N))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      IBMActualQuadraticL2Reconstruction.native_actual H (r i) (r j) N))] with Y hs hi hm hv
  change native a r H N Y = _ at hs
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hi i]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hm i j,Pi.smul_apply,hv i j,smul_eq_mul]

theorem source_pairing_actual (H : ℝ≥0) (N : ℕ) :
    (fun Y => inner ℝ (IBMRawGridSecondChaos.sourceGrid (H/(N+1)) (N+1) Y)
      (rawProduct (direction a r Y) (direction a r Y))) =ᵐ[gaussianProduct] native a r H N := by
  filter_upwards [native_actual a r H N,
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => mixedSource_actual (r i) (r j))),
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j =>
      source_mixed_pairing_ae (H/(N+1)) (N+1) (r i) (r j)))] with Y hn hm he
  rw [pairing_expand,hn]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hij := he i j
  rw [hm i j] at hij
  rw [hij]

theorem native_tendsto (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (native a r H) atTop (𝓝 (reconstruction a r H)) := by
  exact tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_finsetSum Finset.univ fun j _ =>
      (IBMActualQuadraticL2Reconstruction.native_tendsto H (r i) (r j) hH).const_smul (a i*a j)

end OperatorDerivativeRewrite.Foundation.IBMFiniteRidgeQuadraticTesting
