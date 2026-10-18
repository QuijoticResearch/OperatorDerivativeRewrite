import Foundation.PureOrderCompactDecay
import Mathlib.Topology.Algebra.Module.LinearPMap

/-! The actual signed polynomial expectation is not closable in compact-open path topology. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCompactOpenObstruction
open PureOrderCompactDecay HigherHeatPolynomialCylinders HigherHeatPolynomialPathDomain


def parameter (m : ℕ) (T : ℝ≥0) : ℝ := (-1)^(m+1)*(T:ℝ)

theorem parameter_ne_zero (m : ℕ) (T : ℝ≥0) (hT : 0 < T) : parameter m T ≠ 0 := by
  have ht : 0 < (T:ℝ) := hT
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (ne_of_gt ht)

def badCylinder (m : ℕ) (T : ℝ≥0) (n : ℕ) : Cylinder :=
  normalizer (2*m) (parameter m T) n • terminalCylinder^((2*m)*n)

def badObservable (m : ℕ) (T : ℝ≥0) (n : ℕ) : realizedAlgebra :=
  realizationEquiv (badCylinder m T n)

theorem expectation_bad (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    pathExpectation m hm T hT (badObservable m T n) = 1 := by
  rw [badObservable, pathExpectation_apply, badCylinder, map_smul, terminal_moments]
  have he := normalizer_moment (2*m) (by omega) (parameter m T) (parameter_ne_zero m T hT) n
  have hc := congrArg Complex.ofReal he
  simpa only [parameter, Complex.ofReal_mul, Complex.ofReal_one, Complex.real_smul] using hc

theorem observable_val (m : ℕ) (T : ℝ≥0) (n : ℕ) :
    (badObservable m T n).val = family (2*m) (parameter m T) (realize terminalCylinder) n := by
  have he : (badObservable m T n).val = realize (badCylinder m T n) :=
    AlgEquiv.ofInjective_apply realize realize_injective _
  rw [he]
  simp only [badCylinder, family, map_smul, map_pow]

theorem ambient_decay (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => (badObservable m T n).val) atTop (𝓝 (0 : C(Path,ℝ))) := by
  simpa only [observable_val] using family_compact_decay (2*m) (by omega)
    (parameter m T) (parameter_ne_zero m T hT) (realize terminalCylinder)

theorem observable_decay (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (badObservable m T) atTop (𝓝 (0 : realizedAlgebra)) := by
  apply tendsto_subtype_rng.mpr
  exact ambient_decay m hm T hT

theorem expectation_not_continuous (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ¬ Continuous (pathExpectation m hm T hT) := by
  intro h
  have he := (h.tendsto (0 : realizedAlgebra)).comp (observable_decay m hm T hT)
  simp only [Function.comp_def, expectation_bad, map_zero] at he
  have hh := tendsto_nhds_unique he tendsto_const_nhds
  norm_num at hh

theorem graph_pair_decay (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => ((badObservable m T n).val, pathExpectation m hm T hT (badObservable m T n)))
      atTop (𝓝 ((0 : C(Path,ℝ)), (1 : ℂ))) := by
  have he : Tendsto (fun n => pathExpectation m hm T hT (badObservable m T n)) atTop (𝓝 1) := by
    simp only [expectation_bad]
    exact tendsto_const_nhds
  exact (ambient_decay m hm T hT).prodMk_nhds he

theorem no_closed_graph_extension (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (G : Submodule ℝ (C(Path,ℝ) × ℂ)) (hG : IsClosed (G : Set (C(Path,ℝ) × ℂ)))
    (hcore : ∀ F : realizedAlgebra, (F.val, pathExpectation m hm T hT F) ∈ G)
    (hvertical : ∀ z : ℂ, ((0 : C(Path,ℝ)), z) ∈ G → z = 0) : False := by
  have he : ((0 : C(Path,ℝ)), (1 : ℂ)) ∈ G := hG.mem_of_tendsto
    (graph_pair_decay m hm T hT) (Eventually.of_forall (fun n => hcore (badObservable m T n)))
  have hz := hvertical 1 he
  norm_num at hz

theorem no_closed_partial_extension (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (L : C(Path,ℝ) →ₗ.[ℝ] ℂ) (hL : IsClosed (L.graph : Set (C(Path,ℝ) × ℂ)))
    (hcore : ∀ F : realizedAlgebra, (F.val, pathExpectation m hm T hT F) ∈ L.graph) : False := by
  apply no_closed_graph_extension m hm T hT L.graph hL hcore
  intro z hz
  exact LinearPMap.graph_fst_eq_zero_snd L hz rfl


def partialExpectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) : C(Path,ℝ) →ₗ.[ℝ] ℂ where
  domain := realizedAlgebra.toSubmodule
  toFun := (pathExpectation m hm T hT).comp realizedAlgebra.toSubmoduleEquiv.toLinearMap

theorem partialExpectation_core (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : realizedAlgebra) : (F.val, pathExpectation m hm T hT F) ∈ (partialExpectation m hm T hT).graph := by
  apply (LinearPMap.mem_graph_iff' _).mpr
  exact ⟨⟨F.val, F.property⟩, rfl⟩

theorem partialExpectation_not_closable (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ¬ (partialExpectation m hm T hT).IsClosable := by
  intro h
  obtain ⟨L, hL, hle⟩ := LinearPMap.isClosable_iff_exists_closed_extension.mp h
  apply no_closed_partial_extension m hm T hT L hL
  intro F
  exact LinearPMap.le_graph_of_le hle (partialExpectation_core m hm T hT F)


end OperatorDerivativeRewrite.Foundation.HigherHeatCompactOpenObstruction
