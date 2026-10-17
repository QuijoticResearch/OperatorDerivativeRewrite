import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Disintegration.Basic

/-! An actual conditional resampling update, its invariance and idempotence. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.ConditionalResamplingKernel
variable {P E : Type*} [MeasurableSpace P] [MeasurableSpace E]
variable (K : Kernel P E) [IsMarkovKernel K]

def lift : Kernel P (P × E) := Kernel.id ×ₖ K

def update : Kernel (P × E) (P × E) :=
  lift K ∘ₖ Kernel.deterministic Prod.fst measurable_fst

theorem update_markov : IsMarkovKernel (update K) := by
  unfold update lift
  infer_instance

theorem discard_after_lift :
    Kernel.deterministic Prod.fst measurable_fst ∘ₖ lift K = Kernel.id := by
  rw [Kernel.deterministic_comp_eq_map, ← Kernel.fst_eq, lift, Kernel.fst_prod]

theorem update_idempotent : update K ∘ₖ update K = update K := by
  unfold update
  rw [Kernel.comp_assoc, ← Kernel.comp_assoc
    (Kernel.deterministic Prod.fst measurable_fst) (lift K), discard_after_lift,
    Kernel.id_comp]

theorem update_law (J : Measure (P × E)) [SFinite J] :
    update K ∘ₘ J = J.fst ⊗ₘ K := by
  rw [update, ← Measure.comp_assoc, Measure.deterministic_comp_eq_map,
    ← Measure.fst, Measure.compProd_eq_comp_prod]
  rfl

theorem invariant (J : Measure (P × E)) [SFinite J] [J.IsCondKernel K] :
    update K ∘ₘ J = J := by
  rw [update_law, Measure.disintegrate]

theorem boundary_preserved (J : Measure (P × E)) [SFinite J] :
    (update K ∘ₘ J).fst = J.fst := by
  rw [update_law, Measure.fst_compProd]

theorem invariant_iff_conditional (J : Measure (P × E)) [SFinite J] :
    update K ∘ₘ J = J ↔ J.IsCondKernel K := by
  rw [update_law]
  exact ⟨fun h => ⟨h⟩, fun h => h.disintegrate⟩

theorem every_boundary_stationary (π : Measure P) [SFinite π] :
    update K ∘ₘ (π ⊗ₘ K) = π ⊗ₘ K := by
  rw [update_law, Measure.fst_compProd]

theorem boundary_identifies_joint (π τ : Measure P) [SFinite π] [SFinite τ]
    (h : π ⊗ₘ K = τ ⊗ₘ K) : π = τ := by
  have hf := congrArg Measure.fst h
  simpa only [Measure.fst_compProd] using hf

end OperatorDerivativeRewrite.Foundation.ConditionalResamplingKernel
