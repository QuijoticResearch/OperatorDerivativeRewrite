import Foundation.BrownianLocalTimeMesh

/-! The ORIGINAL physical correction has zero strong-L1 square sums along
every deterministic vanishing-mesh partition sequence of [0,T]. Neither
nesting nor equal spacing is assumed, and the local-time term is retained. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal ENNReal BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalOriginalMesh
open InfiniteGaussian IBMPhysicalWeakWiener IBMPhysicalDirac
open BrownianMassContinuousLimit
local instance : InnerProductSpace ℝ Kernel := InnerProductSpace.rclikeToReal ℂ _

def squares {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : ℝ :=
  ∑ i : Fin n, ‖IBMPhysicalPointKernelIto.correctionLimit (τ i.succ) Y-
    IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc) Y‖^2

theorem squares_nonnegative {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (Y : SampleSpace) : 0 ≤ squares τ Y :=
  Finset.sum_nonneg fun i _hi => sq_nonneg _

theorem squares_integrable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : Integrable (squares τ) gaussianProduct :=
  integrable_finsetSum _ fun (i : Fin n) _hi =>
    ((Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.succ))).sub
      (Lp.memLp (IBMPhysicalPointKernelIto.correctionLimit (τ i.castSucc)))).norm.integrable_sq

theorem squares_bound {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : ∀ᵐ Y ∂gaussianProduct,
    squares τ Y ≤ 2*IBMPhysicalMeshVariation.squares τ Y+
      (2*‖dirac 0‖^2)*BrownianLocalTimeMesh.squares τ Y := by
  have h := ae_all_iff.mpr fun i : Fin n => IBMPhysicalOriginalVariation.cell_bound (τ i.castSucc) (τ i.succ)
  filter_upwards [h] with Y hY
  calc
    _ ≤ ∑ i : Fin n, (2*‖IBMPhysicalCorrectedVariation.residual (τ i.succ) Y-
        IBMPhysicalCorrectedVariation.residual (τ i.castSucc) Y‖^2+
          (2*‖dirac 0‖^2)*(limitPath Y (τ i.succ)-limitPath Y (τ i.castSucc))^2) :=
      Finset.sum_le_sum fun i _hi => hY i
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
      IBMPhysicalMeshVariation.squares, BrownianLocalTimeMesh.squares, BrownianLocalTimeMesh.pathSquares]

theorem squares_mean_bound {n : ℕ} (T : ℝ≥0) (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
    (hz : τ 0 = 0) (hend : τ (Fin.last n) = T) :
    (∫ Y, squares τ Y ∂gaussianProduct) ≤
      2*(∫ Y, IBMPhysicalMeshVariation.squares τ Y ∂gaussianProduct)+
        (2*‖dirac 0‖^2)*(∫ Y, BrownianLocalTimeMesh.squares τ Y ∂gaussianProduct) := by
  calc
    _ ≤ ∫ Y, 2*IBMPhysicalMeshVariation.squares τ Y+
        (2*‖dirac 0‖^2)*BrownianLocalTimeMesh.squares τ Y ∂gaussianProduct :=
      integral_mono_ae (squares_integrable τ)
        (((IBMPhysicalMeshVariation.squares_integrable τ).const_mul 2).add
          ((BrownianLocalTimeMesh.squares_integrable T τ hτ hz hend).const_mul _)) (squares_bound τ)
    _ = _ := by rw [integral_add ((IBMPhysicalMeshVariation.squares_integrable τ).const_mul 2)
      ((BrownianLocalTimeMesh.squares_integrable T τ hτ hz hend).const_mul _),
      integral_const_mul, integral_const_mul]

theorem squares_mean_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => ∫ Y, squares (τ N) Y ∂gaussianProduct) atTop (nhds 0) := by
  have hc := IBMPhysicalMeshVariation.squares_mean_tendsto m τ hτ ε hε hmesh (T : ℝ) (fun N => by
    rw [hend N, hz N, NNReal.coe_zero, sub_zero])
  have hl := BrownianLocalTimeMesh.squares_mean_tendsto T m τ hτ hz hend ε hε hmesh
  apply squeeze_zero (fun N => integral_nonneg (squares_nonnegative (τ N)))
    (fun N => squares_mean_bound T (τ N) (hτ N) (hz N) (hend N))
  simpa only [mul_zero, zero_add] using (hc.const_mul 2).add (hl.const_mul (2*‖dirac 0‖^2))

def squaresClass {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : Lp ℝ 1 gaussianProduct :=
  (squares_integrable τ).toL1 (squares τ)

theorem squaresClass_ae {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    squaresClass τ =ᵐ[gaussianProduct] squares τ := (squares_integrable τ).coeFn_toL1

theorem squaresClass_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (hz : ∀ N, τ N 0 = 0)
    (hend : ∀ N, τ N (Fin.last (m N)) = T) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (nhds 0))
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (τ N i.succ : ℝ) - τ N i.castSucc ≤ ε N) :
    Tendsto (fun N => squaresClass (τ N)) atTop (nhds 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero, squaresClass, L1.norm_of_fun_eq_integral_norm,
    Real.norm_of_nonneg (squares_nonnegative _ _)] using
    squares_mean_tendsto T m τ hτ hz hend ε hε hmesh

end OperatorDerivativeRewrite.Foundation.IBMPhysicalOriginalMesh
