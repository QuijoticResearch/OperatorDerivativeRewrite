import Foundation.FourierPathTimeGradient

/-! Actual arbitrary-depth Bochner time spaces and separating bounded-control contractions. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
universe u
namespace OperatorDerivativeRewrite.Foundation.BochnerControlTowers
open FourierPathBoundedControls BochnerTimeControlPairing

structure Space where
  carrier : Type u
  [normed : NormedAddCommGroup carrier]
  [realSpace : NormedSpace ℝ carrier]
  [complete : CompleteSpace carrier]

attribute [instance] Space.normed Space.realSpace Space.complete
instance spaceCoeSort : CoeSort Space (Type u) := ⟨Space.carrier⟩

abbrev of (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] : Space :=
  { carrier := E, normed := inferInstance, realSpace := inferInstance, complete := inferInstance }

abbrev field (B : Space) : Space := of (BochnerTimeControlPairing.Field B)

def tower (B : Space) : ℕ → Space
  | 0 => B
  | n+1 => field (tower B n)

def lift (B C : Space) (L : B →L[ℝ] C) : field B →L[ℝ] field C := L.compLpL 1 volume

theorem lift_norm (B C : Space) (L : B →L[ℝ] C) : ‖lift B C L‖ ≤ ‖L‖ :=
  ContinuousLinearMap.norm_compLpL_le L

theorem pairing_norm (B : Space) (control : Control) : ‖pairing B control‖ ≤ ‖control‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg control)
  exact pairing_bound B control

def evaluate (B : Space) : (n : ℕ) → (Fin n → Control) → (tower B n →L[ℝ] B)
  | 0, _ => ContinuousLinearMap.id ℝ B
  | n+1, controls => (evaluate B n (fun j => controls j.succ)).comp (pairing (tower B n) (controls 0))

theorem evaluate_norm (B : Space) (n : ℕ) (controls : Fin n → Control) :
    ‖evaluate B n controls‖ ≤ ∏ j, ‖controls j‖ := by
  induction n with
  | zero =>
    change ‖ContinuousLinearMap.id ℝ B‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    change ‖(evaluate B n (fun j => controls j.succ)).comp (pairing (tower B n) (controls 0))‖ ≤ _
    have ht : ‖evaluate B n (fun j => controls j.succ)‖ ≤ ∏ j : Fin n, ‖controls j.succ‖ :=
      ih (fun j => controls j.succ)
    have hp : ‖pairing (tower B n) (controls 0)‖ ≤ ‖controls 0‖ := pairing_norm (tower B n) (controls 0)
    calc
      _ ≤ ‖evaluate B n (fun j => controls j.succ)‖*‖pairing (tower B n) (controls 0)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (∏ j : Fin n, ‖controls j.succ‖)*‖controls 0‖ := mul_le_mul ht hp (norm_nonneg _)
        (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
      _ = _ := by rw [Fin.prod_univ_succ]; ring

theorem evaluate_separates (B : Space) (n : ℕ) (x y : tower B n)
    (h : ∀ controls : Fin n → Control, evaluate B n controls x = evaluate B n controls y) : x = y := by
  induction n with
  | zero => exact h (fun j => Fin.elim0 j)
  | succ n ih =>
    apply pairing_injective (tower B n)
    apply ContinuousLinearMap.ext
    intro control
    apply ih
    intro controls
    change evaluate B n controls (pairing (tower B n) control x) =
      evaluate B n controls (pairing (tower B n) control y)
    have hh := h (Fin.cons control controls)
    simp only [evaluate, Fin.cons_zero, Fin.cons_succ] at hh
    exact hh

theorem pairing_lift (B C : Space) (L : B →L[ℝ] C) (control : Control)
    (f : BochnerTimeControlPairing.Field B) : pairing C control (lift B C L f) = L (pairing B control f) :=
  FourierPathTimeGradient.pairing_compLp L control f

end OperatorDerivativeRewrite.Foundation.BochnerControlTowers
