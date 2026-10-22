import Foundation.ClosedOperatorEnergyResolvent
import Foundation.ClosedOperatorEscapeEnergy

/-! Canonical derivatives in the dual of the ORIGINAL adjoint's Hilbert graph.
This extends graph pairings, not the original ambient derivative domain. -/
noncomputable section
open Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.ClosedOperatorGraphDualDerivative
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

abbrev Tests (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) :=
  ↥(ClosedOperatorEnergyResolvent.graphSpace T.adjoint (T.adjoint_isClosed hd))

def field (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) : Tests T hd →L[ℝ] F :=
  (WithLp.fstL 2 ℝ F E).comp
    (ClosedOperatorEnergyResolvent.graphSpace T.adjoint (T.adjoint_isClosed hd)).toSubmodule.subtypeL

def value (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) : Tests T hd →L[ℝ] E :=
  (WithLp.sndL 2 ℝ F E).comp
    (ClosedOperatorEnergyResolvent.graphSpace T.adjoint (T.adjoint_isClosed hd)).toSubmodule.subtypeL

theorem test_graph (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) (w : Tests T hd) :
    (field T hd w, value T hd w) ∈ T.adjoint.graph := w.property

def testOf (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) (v : T.adjoint.domain) : Tests T hd :=
  ⟨WithLp.toLp 2 ((v : F), T.adjoint v), T.adjoint.mem_graph v⟩

def derivative (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) :
    E →L[ℝ] StrongDual ℝ (Tests T hd) :=
  ((value T hd).precomp ℝ).comp (innerSL ℝ)

def embed (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) :
    F →L[ℝ] StrongDual ℝ (Tests T hd) :=
  ((field T hd).precomp ℝ).comp (innerSL ℝ)

theorem derivative_apply (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    (f : E) (w : Tests T hd) : derivative T hd f w = inner ℝ f (value T hd w) := rfl

theorem embed_apply (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    (V : F) (w : Tests T hd) : embed T hd V w = inner ℝ V (field T hd w) := rfl

theorem derivative_original_test (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    (f : E) (v : T.adjoint.domain) :
    derivative T hd f (testOf T hd v) = inner ℝ f (T.adjoint v) := rfl

theorem derivative_norm_le (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) (f : E) :
    ‖derivative T hd f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro w
  rw [derivative_apply]
  exact (norm_inner_le_norm (𝕜 := ℝ) f (value T hd w)).trans
    (mul_le_mul_of_nonneg_left
      (WithLp.norm_snd_le (p := 2) (α := F) (β := E) (w : WithLp 2 (F × E))) (norm_nonneg f))

theorem embed_norm_le (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E)) (V : F) :
    ‖embed T hd V‖ ≤ ‖V‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg V)
  intro w
  rw [embed_apply]
  exact (norm_inner_le_norm (𝕜 := ℝ) V (field T hd w)).trans
    (mul_le_mul_of_nonneg_left
      (WithLp.norm_fst_le (p := 2) (α := F) (β := E) (w : WithLp 2 (F × E))) (norm_nonneg V))

theorem graph_agreement (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    {u : E} {V : F} (hu : (u, V) ∈ T.graph) : embed T hd V = derivative T hd u := by
  ext w
  rw [embed_apply, derivative_apply]
  have hg := test_graph T hd w
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd] at hg
  exact sub_eq_zero.mp ((Submodule.mem_adjoint_iff _ _).mp hg u V hu)

theorem representable_iff_domain (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) (f : E) :
    (∃ V : F, embed T hd V = derivative T hd f) ↔ f ∈ T.domain := by
  constructor
  · rintro ⟨V, hV⟩
    have hm : f ∈ T.adjoint.adjoint.domain := by
      apply T.adjoint.mem_adjoint_domain_of_exists f
      refine ⟨V, fun v => ?_⟩
      have he := congrArg (fun L : StrongDual ℝ (Tests T hd) => L (testOf T hd v)) hV
      exact he
    rwa [HilbertAdjointDomainDensity.closed_bidual T hT hd] at hm
  · intro hf
    exact ⟨T ⟨f, hf⟩, graph_agreement T hd (T.mem_graph ⟨f, hf⟩)⟩

theorem embed_injective (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) : Function.Injective (embed T hd) := by
  intro V W hVW
  apply (HilbertAdjointDomainDensity.closed_adjoint_dense T hT hd).eq_of_inner_left (𝕜 := ℝ)
  intro v hv
  exact congrArg (fun L : StrongDual ℝ (Tests T hd) => L (testOf T hd ⟨v, hv⟩)) hVW

theorem graph_limit (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    {u : ℕ → E} {V : ℕ → F} {f : E}
    (hg : ∀ n, (u n, V n) ∈ T.graph) (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun n => embed T hd (V n)) atTop (𝓝 (derivative T hd f)) := by
  have he (n : ℕ) : embed T hd (V n) = derivative T hd (u n) := graph_agreement T hd (hg n)
  simpa only [Function.comp_def, ← he] using
    (derivative T hd).continuous.tendsto f |>.comp hu

theorem derivative_ne_zero_of_not_domain (T : E →ₗ.[ℝ] F) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set E)) {f : E} (hf : f ∉ T.domain) :
    derivative T hd f ≠ 0 := by
  intro hz
  have he : embed T hd (0 : F) = derivative T hd f :=
    (embed T hd).map_zero.trans hz.symm
  exact hf ((representable_iff_domain T hT hd f).mp ⟨0, he⟩)

theorem graph_error_bound (T : E →ₗ.[ℝ] F) (hd : Dense (T.domain : Set E))
    {u : E} {V : F} (hu : (u, V) ∈ T.graph) (f : E) :
    ‖embed T hd V - derivative T hd f‖ ≤ ‖u - f‖ := by
  rw [graph_agreement T hd hu, ← map_sub]
  exact derivative_norm_le T hd _

end OperatorDerivativeRewrite.Foundation.ClosedOperatorGraphDualDerivative
