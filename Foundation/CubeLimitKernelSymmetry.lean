import Foundation.CubeGaussianGroundEigenvector

/-! Pointwise symmetry and both weighted ground identities of the actual limiting kernel. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeLimitKernelSymmetry
open CubeChartAction CubeBoundaryKernelL2 CubeBoundaryHaarL2 CubeGaussianGroundEigenvector
attribute [local irreducible] CubeWilsonSlab.kernel

theorem localKernel_swap (t : ℝ) (X Y : Boundary) :
    localKernel t (X,Y)=localKernel t (Y,X) := by
  classical
  by_cases hX : X ∈ cutoff t <;> by_cases hY : Y ∈ cutoff t
  · simp only [localKernel,Set.indicator_of_mem (show (X,Y) ∈ cutoff t ×ˢ cutoff t from ⟨hX,hY⟩),
      Set.indicator_of_mem (show (Y,X) ∈ cutoff t ×ˢ cutoff t from ⟨hY,hX⟩)]
    rw [CubeSlabGauge.kernel_symmetric]
  · simp [localKernel,Set.mem_prod,hX,hY]
  · simp [localKernel,Set.mem_prod,hX,hY]
  · simp [localKernel,Set.mem_prod,hX,hY]

theorem kernel_swap (t : ℝ) (X Y : Boundary) :
    CubeBoundaryHaarL2.kernel t (X,Y)=CubeBoundaryHaarL2.kernel t (Y,X) := by
  unfold CubeBoundaryHaarL2.kernel halfDensity
  rw [localKernel_swap,mul_comm (density (t • X)) (density (t • Y))]

theorem limit_swap (X Y : Boundary) :
    CubeBoundaryHaarL2.limit (X,Y)=CubeBoundaryHaarL2.limit (Y,X) := by
  have h := CubeBoundaryHaarL2.kernel_tendsto (X,Y)
  have he : (fun t : ℝ => CubeBoundaryHaarL2.kernel t (X,Y))=
      (fun t : ℝ => CubeBoundaryHaarL2.kernel t (Y,X)) := funext (fun t => kernel_swap t X Y)
  rw [he] at h
  exact tendsto_nhds_unique h (CubeBoundaryHaarL2.kernel_tendsto (Y,X))

theorem column_ground (Y : Boundary) :
    (∫ X : Boundary,CubeBoundaryHaarL2.limit (X,Y)*actualState X)=eigenvalue*actualState Y := by
  simp_rw [limit_swap _ Y]
  exact actual_row_ground Y

theorem column_ground_integrable (Y : Boundary) :
    Integrable (fun X : Boundary => CubeBoundaryHaarL2.limit (X,Y)*actualState X) := by
  simp_rw [limit_swap _ Y]
  exact actual_row_ground_integrable Y

end OperatorDerivativeRewrite.Foundation.CubeLimitKernelSymmetry
