import Foundation.HigherHeatPrefixPowerIdentity
import Mathlib.Analysis.Normed.MulAction

/-! Continuous signed-dual curves for all coordinate powers, in the existing dual.
The recursive prefix identity uses auxiliary fields that may anticipate. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialDualCurve
open HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality HigherHeatPrefixFields
open HigherHeatAllProductChannels HigherHeatDyadicTimeDensity

def powerFunction (m : ℕ) (T : ℝ≥0) (a : Dual) : ℕ → Interval → Dual
  | 0 => fun _ => a
  | r+1 => fun t => ∑ k ∈ Finset.range (2*m), r.descFactorial k • productChannel m T k
      (segment 0 (t:ℝ) (powerFunction m T a (r-k) t))
termination_by r => r

theorem finite_sum_lipschitz {ι : Type*} (s : Finset ι) (f : ι → Interval → Dual)
    (h : ∀ i ∈ s, ∃ C : ℝ≥0, LipschitzWith C (f i)) :
    ∃ C : ℝ≥0, LipschitzWith C (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using (LipschitzWith.const (0:Dual))⟩
  | @insert i s hi ih =>
    obtain ⟨Ci, hCi⟩ := h i (Finset.mem_insert_self _ _)
    obtain ⟨Cs, hCs⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    exact ⟨Ci+Cs, by simpa only [Finset.sum_insert hi] using hCi.add hCs⟩

theorem powerFunction_lipschitz (m : ℕ) (T : ℝ≥0) (a : Dual) (r : ℕ) :
    ∃ C : ℝ≥0, LipschitzWith C (powerFunction m T a r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero => exact ⟨0, by simpa only [powerFunction] using (LipschitzWith.const a)⟩
    | succ r =>
      rw [powerFunction]
      apply finite_sum_lipschitz
      intro k _
      obtain ⟨C, hC⟩ := ih (r-k) (by omega)
      let f : C(Interval,Dual) := ⟨powerFunction m T a (r-k), hC.continuous⟩
      have hp := prefix_lipschitz _ C ‖f‖₊ hC (fun t => f.norm_coe_le_norm t)
      have hc := (productChannel m T k).lipschitzWith.comp hp
      have hs := (lipschitzWith_smul (r.descFactorial k:ℝ)).comp hc
      exact ⟨_, by simpa only [Function.comp_def, Nat.cast_smul_eq_nsmul] using hs⟩

def powerConstant (m : ℕ) (T : ℝ≥0) (a : Dual) (r : ℕ) : ℝ≥0 :=
  Classical.choose (powerFunction_lipschitz m T a r)

theorem powerFunction_lipschitz_with (m : ℕ) (T : ℝ≥0) (a : Dual) (r : ℕ) :
    LipschitzWith (powerConstant m T a r) (powerFunction m T a r) :=
  Classical.choose_spec (powerFunction_lipschitz m T a r)

def powerCurve (m : ℕ) (T : ℝ≥0) (a : Dual) (r : ℕ) : C(Interval,Dual) :=
  ⟨powerFunction m T a r, (powerFunction_lipschitz_with m T a r).continuous⟩

end OperatorDerivativeRewrite.Foundation.HigherHeatPolynomialDualCurve
