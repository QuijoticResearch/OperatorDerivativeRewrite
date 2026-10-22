import Foundation.HilbertAdjointDomainDensity
import Foundation.HilbertRepresentation

/-! Strong value convergence to a point outside a closed densely defined
Hilbert operator domain forces its graph-output norms to escape to infinity. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ClosedOperatorEscapeEnergy
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem graph_pairing (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    {u : E} {v : F} (hu : (u, v) ∈ T.graph) (w : T.adjoint.domain) :
    inner ℝ u (T.adjoint w) = inner ℝ v (w : F) := by
  have ha := T.adjoint.mem_graph w
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd] at ha
  exact (sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp ha u v hu)).symm

theorem mem_domain_of_frequently_bounded_graph (T : E →ₗ.[ℝ] F)
    (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    {u : ℕ → E} {v : ℕ → F} {f : E}
    (hg : ∀ n, (u n, v n) ∈ T.graph) (hu : Tendsto u atTop (𝓝 f))
    (C : ℝ) (hb : ∃ᶠ n in atTop, ‖v n‖ ≤ C) : f ∈ T.domain := by
  have hL (w : T.adjoint.domain) : ‖inner ℝ f (T.adjoint w)‖ ≤ C * ‖(w : F)‖ := by
    have hc : Continuous (fun x : E => ‖inner ℝ x (T.adjoint w)‖) :=
      (continuous_id.inner continuous_const).norm
    apply le_of_tendsto_of_frequently (hc.tendsto f |>.comp hu)
    apply hb.mono
    intro n hn
    change ‖inner ℝ (u n) (T.adjoint w)‖ ≤ C * ‖(w : F)‖
    rw [graph_pairing T hd (hg n) w]
    exact (norm_inner_le_norm (𝕜 := ℝ) (v n) (w : F)).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  have hm : f ∈ T.adjoint.adjoint.domain := by
    apply (HilbertRepresentation.adjoint_domain_iff_pairing_bound T.adjoint
      (HilbertAdjointDomainDensity.closed_adjoint_dense T hT hd) f).mpr
    have hC : 0 ≤ C := by
      obtain ⟨n, hn⟩ := hb.exists
      exact (norm_nonneg (v n)).trans hn
    exact ⟨C, hC, fun w => by simpa only [Real.norm_eq_abs] using hL w⟩
  rwa [HilbertAdjointDomainDensity.closed_bidual T hT hd] at hm

theorem output_norm_tendsto_atTop (T : E →ₗ.[ℝ] F)
    (hT : T.IsClosed) (hd : Dense (T.domain : Set E))
    {u : ℕ → E} {v : ℕ → F} {f : E}
    (hg : ∀ n, (u n, v n) ∈ T.graph) (hu : Tendsto u atTop (𝓝 f))
    (hf : f ∉ T.domain) : Tendsto (fun n => ‖v n‖) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  by_contra h
  have hb : ∃ᶠ n in atTop, ‖v n‖ ≤ C :=
    (not_eventually.mp h).mono (fun n hn => (not_le.mp hn).le)
  exact hf (mem_domain_of_frequently_bounded_graph T hT hd hg hu C hb)

end OperatorDerivativeRewrite.Foundation.ClosedOperatorEscapeEnergy
