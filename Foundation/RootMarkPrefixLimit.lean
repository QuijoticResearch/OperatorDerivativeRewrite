import Foundation.RootMarkStochasticIntegral
import Mathlib.Probability.Martingale.Convergence

/-! The actual prefixes generate the full mark source and recover integrable real variables. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.RootMarkPrefixLimit
open RootMarkStochasticIntegral
open MarkedRootRenewalProcess (MarkSample marks)

theorem history_generates : (⨆ n : ℕ, history n) = (inferInstance : MeasurableSpace MarkSample) := by
  apply le_antisymm (iSup_le fun n => history.le n)
  change (⨆ j : ℕ, MeasurableSpace.comap (fun η : MarkSample => η j) inferInstance) ≤ _
  refine iSup_le fun j => ?_
  have hj : Measurable[history (j+1)] (fun η : MarkSample => η j) :=
    (measurable_pi_apply (⟨j,Nat.lt_succ_self j⟩ : Fin (j+1))).comp (prefix_past (j+1))
  exact hj.comap_le.trans (le_iSup (fun n : ℕ => history n) (j+1))

theorem real_condExp_limit (Y : MarkSample → ℝ) (hY : Integrable Y marks)
    (hm : StronglyMeasurable Y) :
    Tendsto (fun n : ℕ => eLpNorm (marks[Y | history n]-Y) 1 marks) atTop (𝓝 0) := by
  apply hY.tendsto_eLpNorm_condExp (ℱ := history)
  rwa [history_generates]

theorem real_condExp_ae_limit (Y : MarkSample → ℝ) (hY : Integrable Y marks)
    (hm : StronglyMeasurable Y) :
    ∀ᵐ η ∂marks, Tendsto (fun n : ℕ => marks[Y | history n] η) atTop (𝓝 (Y η)) := by
  apply hY.tendsto_ae_condExp (ℱ := history)
  rwa [history_generates]

end OperatorDerivativeRewrite.Foundation.RootMarkPrefixLimit
