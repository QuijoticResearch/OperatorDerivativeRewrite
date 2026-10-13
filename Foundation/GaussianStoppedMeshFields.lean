import Foundation.GaussianRefiningPartitions
import Foundation.GaussianStoppedSmoothFields

/-! All first- and second-derivative approximations for an arbitrary C2 stopped
cylinder now use caps of ONE common refining mesh. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianStoppedMeshFields
open InfiniteGaussian GaussianTimeProcess GaussianPredictableFull
open GaussianStoppedSmoothFields FiniteCovarianceHessian
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (Φ : (ι → ℝ) → ℝ) (hΦ : ContDiff ℝ 2 Φ) (K0 K1 : ℝ≥0)
  (h0 : ∀ x, ‖fderiv ℝ Φ x‖₊ ≤ K0) (h1 : ∀ x, ‖hessian Φ x‖₊ ≤ K1)
  (r : ι → ℝ≥0)

def gradientSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : GaussianL2 :=
  ∑ i, itoIntegral (GaussianRefiningPartitions.predictableStep (gradientValue Φ hΦ K0 h0 r i)
    (gradientValue_past Φ hΦ K0 h0 r i) (fun k => min (τ k) (r i)))

def hessianSum {n : ℕ} (τ : Fin (n+1) → ℝ≥0) : GaussianL2 :=
  (1/2:ℝ) • ∑ i, ∑ j, ∑ k : Fin n,
    ((min (τ k.succ) (min (r i) (r j)):ℝ)-min (τ k.castSucc) (min (r i) (r j))) •
      hessianValue Φ hΦ K1 h1 r i j (min (τ k.castSucc) (min (r i) (r j)))

theorem gradientSum_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => gradientSum Φ hΦ K0 h0 r (τ N)) atTop
      (𝓝 (itoIntegral (gradientField Φ hΦ K0 h0 r T))) := by
  simp only [gradientSum, gradientField, map_sum]
  exact tendsto_finsetSum Finset.univ (fun i _ =>
    GaussianRefiningPartitions.capped_integral_step_tendsto _
      (gradientValue_continuous Φ hΦ K0 h0 r i) (gradientValue_past Φ hΦ K0 h0 r i)
      m τ hτ T (r i) hstart hend ε hlim hmesh)

theorem hessianSum_tendsto (m : ℕ → ℕ) (τ : (N : ℕ) → Fin (m N+1) → ℝ≥0)
    (hτ : ∀ N, Monotone (τ N)) (T : ℝ≥0)
    (hstart : ∀ N, τ N 0 = 0) (hend : ∀ N, τ N (Fin.last (m N)) = T)
    (ε : ℕ → ℝ) (hlim : Tendsto ε atTop (𝓝 0))
    (hmesh : ∀ N (k : Fin (m N)), (τ N k.succ:ℝ)-τ N k.castSucc ≤ ε N) :
    Tendsto (fun N => hessianSum Φ hΦ K1 h1 r (τ N)) atTop
      (𝓝 (hessianDrift Φ hΦ K1 h1 r T)) := by
  apply Filter.Tendsto.const_smul
  apply tendsto_finsetSum Finset.univ
  intro i _
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact GaussianRefiningPartitions.capped_drift_sum_tendsto _
    (hessianValue_continuous Φ hΦ K1 h1 r i j) m τ hτ T (min (r i) (r j))
    hstart hend ε hlim hmesh

end OperatorDerivativeRewrite.Foundation.GaussianStoppedMeshFields
