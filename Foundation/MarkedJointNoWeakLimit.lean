import Foundation.MarkedSignedCylinderBridge
import Foundation.ComplexRootPoissonNoWeakLimit

/-! Holomorphic cylinder convergence coexists with actual joint probability non-tightness. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedJointNoWeakLimit
open MarkedRootRenewalProcess (probability)
open MarkedRenewalMartingale MarkedSignedCylinderBridge ComplexRootHeatTransformLimit

theorem jointLaw_first_marginal (a : ℝ) (s t : ℝ≥0) :
    (jointLaw a s t).map Prod.fst = ComplexRootPoissonLaw.law s a := by
  rw [jointLaw,Measure.map_map measurable_fst
    ((process_measurable a s).prodMk (process_measurable a t))]
  exact process_law a s

def probabilityLaw (h : ℝ≥0) (n : ℕ) : ProbabilityMeasure (ℂ × ℂ) :=
  (jointLaw (amplitude 1 n) (n : ℝ≥0) ((n : ℝ≥0)*(1+h))).toProbabilityMeasure

theorem not_tight_reindexed (h : ℝ≥0) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    ¬ IsTightMeasureSet (Set.range (fun n : ℕ =>
      jointLaw (amplitude 1 (φ n)) (φ n : ℝ≥0) ((φ n : ℝ≥0)*(1+h)))) := by
  intro ht
  have he := ht.map (continuous_fst : Continuous (Prod.fst : ℂ × ℂ → ℂ))
  rw [← Set.range_comp] at he
  apply ComplexRootPoissonNoWeakLimit.not_tight_reindexed 1 (by norm_num) φ hφ
  simpa only [Function.comp_def,jointLaw_first_marginal] using he

theorem not_tight (h : ℝ≥0) :
    ¬ IsTightMeasureSet (Set.range (fun n : ℕ =>
      jointLaw (amplitude 1 n) (n : ℝ≥0) ((n : ℝ≥0)*(1+h)))) :=
  not_tight_reindexed h id tendsto_id

theorem not_tendsto_reindexed (h : ℝ≥0) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (μ : ProbabilityMeasure (ℂ × ℂ)) :
    ¬ Tendsto (fun n => probabilityLaw h (φ n)) atTop (𝓝 μ) := by
  intro ht
  have hc := ht.isCompact_insert_range
  have hcl : IsCompact (closure (insert μ (Set.range (fun n => probabilityLaw h (φ n))))) := by
    rw [hc.isClosed.closure_eq]
    exact hc
  have hS := isTightMeasureSet_of_isCompact_closure hcl
  apply not_tight_reindexed h φ hφ
  apply hS.subset
  rintro ν ⟨n,rfl⟩
  exact ⟨probabilityLaw h (φ n),Set.mem_insert_of_mem μ ⟨n,rfl⟩,rfl⟩

theorem not_tendsto (h : ℝ≥0) (μ : ProbabilityMeasure (ℂ × ℂ)) :
    ¬ Tendsto (probabilityLaw h) atTop (𝓝 μ) :=
  not_tendsto_reindexed h id tendsto_id μ

end OperatorDerivativeRewrite.Foundation.MarkedJointNoWeakLimit
