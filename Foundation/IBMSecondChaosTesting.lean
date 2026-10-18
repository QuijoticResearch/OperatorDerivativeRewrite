import Foundation.IBMQuarticSecondChaos
import Foundation.GaussianQuadraticMatrixApproximation

/-! Quadratic Wick tests separate the existing completed second chaos.
The density input is the verified native matrix approximation theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSecondChaosTesting
open InfiniteGaussian GaussianNumberSectors GaussianTimeSpaceHermite IBMQuarticSecondChaos
open GaussianQuadraticSourceHodge GaussianQuadraticMatrixApproximation GaussianFiniteQuadraticL4

theorem cross_eq_mixedTarget (u v : CoefficientSpace) : cross u v = mixedTarget u v := by
  apply Lp.ext
  filter_upwards [cross_coeFn u v, mixedTarget_coeFn u v] with ω hc hm
  rw [hc, hm]

/-- No new second-chaos density assumption is introduced. -/
theorem eq_zero_of_wick_tests (f : GaussianL2) (hf : f ∈ sector 2)
    (htest : ∀ k : CoefficientSpace, inner ℝ f (wick k 2 : GaussianL2) = 0) : f = 0 := by
  have hm (u v : CoefficientSpace) : inner ℝ f (mixedTarget u v) = 0 := by
    rw [← cross_eq_mixedTarget, cross]
    simp only [inner_smul_right, inner_sub_right, htest, sub_zero, mul_zero]
  simp only [mixedTarget] at hm
  have hb (N : ℕ) : inner ℝ f (boxCore (Finset.range N)
      ⟨GaussianDivergenceRecovery.recovery f,
        GaussianQuadraticRecoverySurjectivity.recovery_second_chaos_linear hf⟩ : GaussianL2) = 0 := by
    simp only [boxCore, matrixCore, Submodule.coe_sum, Submodule.coe_smul]
    simp only [inner_sum, inner_smul_right, hm,
      mul_zero, Finset.sum_const_zero]
  have hc : Continuous (fun z : GaussianL2 => inner ℝ f z) :=
    continuous_const.inner continuous_id
  have ht := hc.continuousAt.tendsto.comp (boxCore_tendsto f hf)
  have hz : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (inner ℝ f f)) := by
    simpa only [Function.comp_def, hb] using ht
  exact inner_self_eq_zero.mp (tendsto_nhds_unique hz tendsto_const_nhds)

theorem projection_eq_of_wick_tests (f g : GaussianL2) (hg : g ∈ sector 2)
    (htest : ∀ k : CoefficientSpace,
      inner ℝ f (wick k 2 : GaussianL2) = inner ℝ g (wick k 2 : GaussianL2)) :
    projection 2 f = g := by
  apply sub_eq_zero.mp
  apply eq_zero_of_wick_tests _ ((sector 2).sub_mem (projection_mem 2 f) hg)
  intro k
  have hp := (sector 2).starProjection_inner_eq_zero f (wick k 2 : GaussianL2)
    (IBMCubicFirstChaos.wick_mem_sector k 2)
  change inner ℝ (f-projection 2 f) (wick k 2 : GaussianL2) = 0 at hp
  rw [inner_sub_left] at hp ⊢
  rw [← htest]
  linarith

theorem cross_mem_sector (u v : CoefficientSpace) : cross u v ∈ sector 2 := by
  exact (sector 2).smul_mem _ ((sector 2).sub_mem ((sector 2).sub_mem
    (IBMCubicFirstChaos.wick_mem_sector (u+v) 2) (IBMCubicFirstChaos.wick_mem_sector u 2))
    (IBMCubicFirstChaos.wick_mem_sector v 2))

theorem cross_wick_pairing (u v k : CoefficientSpace) :
    inner ℝ (cross u v) (wick k 2 : GaussianL2) =
      2*inner ℝ u k*inner ℝ v k := by
  simp only [cross, real_inner_smul_left, inner_sub_left, wick_inner]
  norm_num
  simp only [inner_add_left]
  ring

end OperatorDerivativeRewrite.Foundation.IBMSecondChaosTesting
