import Foundation.ProjectedFormClosability
import Foundation.MixedAtomicDerivativeOperator
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Finite-dimensional restrictions can all be closable while their union is not. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteWindowClosabilityBoundary
open WeightedFormClosability MixedAtomicGradient MixedAtomicDerivativeOperator
set_option backward.isDefEq.respectTransparency false

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def windowMap (T : X →ₗ.[ℝ] Y) (W : Submodule ℝ X) (hW : W ≤ T.domain) : W →ₗ[ℝ] Y :=
  T.toFun.comp (Submodule.inclusion hW)

theorem finite_window_seqClosable (T : X →ₗ.[ℝ] Y)
    (W : Submodule ℝ X) (hW : W ≤ T.domain) [FiniteDimensional ℝ W] :
    SeqClosable W.subtype (windowMap T W hW) := by
  intro f hf y hy
  have hfw : Tendsto f atTop (𝓝 0) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hn := hf.norm
    change Tendsto (fun n => ‖f n‖) atTop (𝓝 ‖(0 : X)‖) at hn
    simpa only [sub_zero, norm_zero] using hn
  have hD := ((windowMap T W hW).continuous_of_finiteDimensional.tendsto 0).comp hfw
  exact tendsto_nhds_unique hy (by simpa only [Function.comp_def, map_zero] using hD)

theorem finite_window_formClosable [CompleteSpace Y] (T : X →ₗ.[ℝ] Y)
    (W : Submodule ℝ X) (hW : W ≤ T.domain) [FiniteDimensional ℝ W]
    (κ : ℝ) (hκ : 0 ≤ κ) : FormClosable κ W.subtype (windowMap T W hW) :=
  seqClosable_implies_nonnegative_form (finite_window_seqClosable T W hW) κ hκ

theorem finite_windows_cover (T : X →ₗ.[ℝ] Y) (u : T.domain) :
    ∃ (W : Submodule ℝ X) (_hW : W ≤ T.domain),
      FiniteDimensional ℝ W ∧ (u : X) ∈ W := by
  refine ⟨Submodule.span ℝ {(u : X)}, ?_, inferInstance, Submodule.subset_span (by simp)⟩
  exact Submodule.span_le.mpr (by
    intro x hx
    have hx' : x = (u : X) := Set.mem_singleton_iff.mp hx
    rw [hx']
    change (u : X) ∈ T.domain
    exact u.property)

abbrev MixedL2 := Lp ℝ 2 μ

theorem mixed_finite_windows_closable
    (W : Submodule ℝ MixedL2) (hW : W ≤ derivativeOperator.domain)
    [FiniteDimensional ℝ W] (κ : ℝ) (hκ : 0 ≤ κ) :
    FormClosable κ W.subtype (windowMap derivativeOperator W hW) :=
  finite_window_formClosable derivativeOperator W hW κ hκ

theorem mixed_windows_cover (u : derivativeOperator.domain) :
    ∃ (W : Submodule ℝ MixedL2) (_hW : W ≤ derivativeOperator.domain),
      FiniteDimensional ℝ W ∧ (u : MixedL2) ∈ W :=
  finite_windows_cover derivativeOperator u

theorem mixed_global_not_seqClosable :
    ¬ SeqClosable derivativeOperator.domain.subtype derivativeOperator.toFun := by
  intro h
  let f (n : ℕ) : derivativeOperator.domain :=
    ⟨input (jetCore n), operator_domain (jetCore n)⟩
  have hin : Tendsto (fun n => ((f n : derivativeOperator.domain) : MixedL2))
      atTop (𝓝 0) := input_jets_tendsto_zero
  have hout : Tendsto (fun n => derivativeOperator (f n)) atTop (𝓝 atomClass) := by
    simpa only [f, operator_agrees] using output_jets_tendsto_atom
  exact atomClass_nonzero (h f hin atomClass hout)

theorem mixed_global_not_formClosable (κ : ℝ) (hκ : 0 < κ) :
    ¬ FormClosable κ derivativeOperator.domain.subtype derivativeOperator.toFun := by
  intro h
  exact mixed_global_not_seqClosable (form_implies_seqClosable κ hκ h)

end OperatorDerivativeRewrite.Foundation.FiniteWindowClosabilityBoundary
