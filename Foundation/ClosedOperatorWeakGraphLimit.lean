import Foundation.ClosedOperatorEscapeEnergy
import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-! Weak output convergence for bounded genuine closed-Hilbert-operator graphs.
Strong convergence of values and bounded outputs do not assert strong output convergence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ClosedOperatorWeakGraphLimit
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem adjoint_pairing_tendsto (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    {u : ℕ → E} {v : ℕ → F} {f : E} {g : F}
    (hg : ∀ n, (u n, v n) ∈ T.graph) (hfg : (f, g) ∈ T.graph)
    (hu : Tendsto u atTop (𝓝 f)) (w : T.adjoint.domain) :
    Tendsto (fun n => inner ℝ (v n) (w : F)) atTop (𝓝 (inner ℝ g (w : F))) := by
  have he : (fun n => inner ℝ (v n) (w : F)) =
      fun n => inner ℝ (u n) (T.adjoint w) :=
    funext fun n => (ClosedOperatorEscapeEnergy.graph_pairing T hd (hg n) w).symm
  rw [he, ← ClosedOperatorEscapeEnergy.graph_pairing T hd hfg w]
  exact hu.inner tendsto_const_nhds

theorem pairing_tendsto (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    {u : ℕ → E} {v : ℕ → F} {f : E} {g : F}
    (hg : ∀ n, (u n, v n) ∈ T.graph) (hfg : (f, g) ∈ T.graph)
    (hu : Tendsto u atTop (𝓝 f)) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖v n‖ ≤ C) (w : F) :
    Tendsto (fun n => inner ℝ (v n) w) atTop (𝓝 (inner ℝ g w)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let M := C + ‖g‖
  have hM : 0 ≤ M := add_nonneg hC (norm_nonneg g)
  have hMp : 0 < M + 1 := by linarith
  have hδ : 0 < ε / (2 * (M + 1)) := div_pos hε (by positivity)
  obtain ⟨z, hz, hdist⟩ := (HilbertAdjointDomainDensity.closed_adjoint_dense T hT hd).exists_dist_lt w hδ
  have hn : ‖w - z‖ < ε / (2 * (M + 1)) := by simpa only [dist_eq_norm] using hdist
  have hsmall : M * ‖w - z‖ < ε / 2 := by
    have hp := mul_lt_mul_of_pos_left hn hMp
    have he : (M + 1) * (ε / (2 * (M + 1))) = ε / 2 := by field_simp
    rw [he] at hp
    nlinarith [norm_nonneg (w - z)]
  have ha := adjoint_pairing_tendsto T hd hg hfg hu ⟨z, hz⟩
  filter_upwards [Metric.tendsto_nhds.mp ha (ε / 2) (half_pos hε)] with n hn
  have hn' : |inner ℝ (v n - g) z| < ε / 2 := by
    simpa only [Real.dist_eq, inner_sub_left] using hn
  have hv : ‖v n - g‖ ≤ M := (norm_sub_le _ _).trans (add_le_add (hb n) le_rfl)
  rw [Real.dist_eq, ← inner_sub_left]
  calc
    |inner ℝ (v n - g) w| = |inner ℝ (v n - g) (w - z) + inner ℝ (v n - g) z| := by
      rw [← inner_add_right, sub_add_cancel]
    _ ≤ |inner ℝ (v n - g) (w - z)| + |inner ℝ (v n - g) z| := by
      simpa only [Real.norm_eq_abs] using
        norm_add_le (inner ℝ (v n - g) (w - z)) (inner ℝ (v n - g) z)
    _ ≤ ‖v n - g‖ * ‖w - z‖ + |inner ℝ (v n - g) z| := by
      have hi : |inner ℝ (v n - g) (w - z)| ≤ ‖v n - g‖ * ‖w - z‖ := by
        simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (v n - g) (w - z)
      exact add_le_add hi le_rfl
    _ ≤ M * ‖w - z‖ + |inner ℝ (v n - g) z| :=
      add_le_add (mul_le_mul_of_nonneg_right hv (norm_nonneg _)) le_rfl
    _ < ε := by linarith

theorem weak_tendsto (T : E →ₗ.[ℝ] F) (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    {u : ℕ → E} {v : ℕ → F} {f : E} {g : F}
    (hg : ∀ n, (u n, v n) ∈ T.graph) (hfg : (f, g) ∈ T.graph)
    (hu : Tendsto u atTop (𝓝 f)) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ n, ‖v n‖ ≤ C) :
    Tendsto (fun n => (v n : WeakBilin (innerₗ F))) atTop
      (@nhds (WeakBilin (innerₗ F)) (WeakBilin.instTopologicalSpace (innerₗ F)) g) := by
  have hi : Function.Injective (innerₗ F) := by
    intro a b he
    have hs : inner ℝ (a - b) (a - b) = 0 := by
      rw [inner_sub_left]
      exact sub_eq_zero.mpr (congrArg (fun L : F →ₗ[ℝ] ℝ => L (a - b)) he)
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hs)
  exact (WeakBilin.tendsto_iff_forall_eval_tendsto (innerₗ F) hi).mpr
    (pairing_tendsto T hT hd hg hfg hu C hC hb)

end OperatorDerivativeRewrite.Foundation.ClosedOperatorWeakGraphLimit
