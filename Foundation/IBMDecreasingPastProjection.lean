import Foundation.IBMIntrinsicMartingaleEndpoint

/-! Strong convergence for decreasing ACTUAL IBM past spaces, obtained from
the existing increasing-projection theorem by taking orthogonal complements. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMDecreasingPastProjection
open IBMNaturalFiltrationObstruction IBMTimeAveragedObservable
set_option backward.isDefEq.respectTransparency false

def intersectionSpace (τ : ℕ → ℝ≥0) : Submodule ℝ JointL2 :=
  (⨆ n, (past (τ n))ᗮ).topologicalClosureᗮ

private instance intersectionProjection (τ : ℕ → ℝ≥0) :
    (intersectionSpace τ).HasOrthogonalProjection := by
  unfold intersectionSpace
  infer_instance

theorem intersectionSpace_eq_iInf (τ : ℕ → ℝ≥0) :
    intersectionSpace τ = ⨅ n, past (τ n) := by
  unfold intersectionSpace
  rw [Submodule.orthogonal_closure, ← Submodule.iInf_orthogonal]
  simp only [Submodule.orthogonal_orthogonal]

theorem projection_tendsto (τ : ℕ → ℝ≥0) (hτ : Antitone τ) (f : JointL2) :
    Tendsto (fun n => (past (τ n)).starProjection f) atTop
      (𝓝 ((intersectionSpace τ).starProjection f)) := by
  have hm : Monotone (fun n => (past (τ n))ᗮ) := by
    intro i j hij
    apply Submodule.orthogonal_le
    intro g hg
    exact hg.mono (naturalFiltration.mono (hτ hij))
  have ht := Submodule.starProjection_tendsto_closure_iSup (fun n => (past (τ n))ᗮ) hm f
  have hc : Tendsto (fun _ : ℕ => f) atTop (𝓝 f) := tendsto_const_nhds
  have hs := hc.sub ht
  have he (n : ℕ) : f - (past (τ n))ᗮ.starProjection f = (past (τ n)).starProjection f := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hl : f - (⨆ n, (past (τ n))ᗮ).topologicalClosure.starProjection f =
      (intersectionSpace τ).starProjection f :=
    (Submodule.starProjection_orthogonal_val f).symm
  simpa only [he, hl] using hs

theorem valueClass_tendsto (τ : ℕ → ℝ≥0) (hτ : Antitone τ) (T : ℝ≥0)
    (hT : ∀ n, τ n ≤ T) :
    Tendsto (fun n => (IBMIntrinsicQuadraticMartingale.valueClass (τ n) : JointL2)) atTop
      (𝓝 ((intersectionSpace τ).starProjection
        (IBMIntrinsicQuadraticMartingale.valueClass T : JointL2))) := by
  have ht := projection_tendsto τ hτ (IBMIntrinsicQuadraticMartingale.valueClass T : JointL2)
  simpa only [IBMIntrinsicMartingaleEndpoint.projection_value (hT _)] using ht

end OperatorDerivativeRewrite.Foundation.IBMDecreasingPastProjection
