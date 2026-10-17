import Foundation.BochnerControlTowers
import Foundation.FourierPathGradientCommutation

/-! Actual all-depth integrable time fields and their closed-derivative contractions. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeTowers
open HigherHeatDyadicLaws HigherHeatContinuousCylinders HigherHeatFourierBanach
open FourierPathBoundedControls BochnerTimeControlPairing BochnerControlTowers
open FourierPathTimeGradient FourierPathControlGradient FourierPathGradientCommutation
open FourierPathDirectionalOperator HigherHeatFourierPathSemigroup

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

abbrev base : Space := BochnerControlTowers.of (TestSpace levels ξ)

def first (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    base levels ξ →L[ℝ] field (base levels ξ) :=
  (timeGradient levels ξ m hm T hT).restrictScalars ℝ

theorem first_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    ‖first levels ξ m hm T hT‖ ≤ 1+(T:ℝ)⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro q
  exact timeGradient_bound levels ξ m hm T hT q

def density (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (n : ℕ) → (base levels ξ →L[ℝ] tower (base levels ξ) n)
  | 0 => ContinuousLinearMap.id ℝ (base levels ξ)
  | n+1 => (lift (base levels ξ) (tower (base levels ξ) n) (density m hm T hT n)).comp
      (first levels ξ m hm T hT)

theorem density_norm (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (n : ℕ) :
    ‖density levels ξ m hm T hT n‖ ≤ (1+(T:ℝ)⁻¹)^n := by
  induction n with
  | zero =>
    change ‖ContinuousLinearMap.id ℝ (base levels ξ)‖ ≤ 1
    exact ContinuousLinearMap.norm_id_le
  | succ n ih =>
    change ‖(lift (base levels ξ) (tower (base levels ξ) n) (density levels ξ m hm T hT n)).comp
      (first levels ξ m hm T hT)‖ ≤ _
    calc
      _ ≤ ‖lift (base levels ξ) (tower (base levels ξ) n) (density levels ξ m hm T hT n)‖*
          ‖first levels ξ m hm T hT‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (1+(T:ℝ)⁻¹)^n*(1+(T:ℝ)⁻¹) := mul_le_mul
        ((lift_norm _ _ _).trans ih) (first_norm levels ξ m hm T hT) (norm_nonneg _) (by positivity)
      _ = _ := (pow_succ _ _).symm

def orderedDerivative (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    (n : ℕ) → (Fin n → Control) → TestSpace levels ξ → TestSpace levels ξ
  | 0, _, q => q
  | n+1, controls, q => orderedDerivative m hm T hT n (fun j => controls j.succ)
      (gradient levels ξ m hm T hT q (controls 0))

theorem density_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (controls : Fin n → Control) (q : TestSpace levels ξ) :
    evaluate (base levels ξ) n controls (density levels ξ m hm T hT n q) =
      orderedDerivative levels ξ m hm T hT n controls q := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    change evaluate (base levels ξ) n (fun j => controls j.succ)
      (pairing (tower (base levels ξ) n) (controls 0)
        (lift (base levels ξ) (tower (base levels ξ) n) (density levels ξ m hm T hT n)
          (first levels ξ m hm T hT q))) = _
    rw [pairing_lift]
    change evaluate (base levels ξ) n (fun j => controls j.succ)
      (density levels ξ m hm T hT n
        (pairing (TestSpace levels ξ) (controls 0) (timeGradient levels ξ m hm T hT q))) = _
    rw [timeGradient_pairing]
    exact ih _ _

theorem density_unique (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (q : TestSpace levels ξ) (K : tower (base levels ξ) n)
    (hK : ∀ controls, evaluate (base levels ξ) n controls K =
      orderedDerivative levels ξ m hm T hT n controls q) : K = density levels ξ m hm T hT n q := by
  apply evaluate_separates (base levels ξ) n
  intro controls
  exact (hK controls).trans (density_pairing levels ξ m hm T hT n controls q).symm

theorem ordered_preserves_graph (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (controls : Fin n → Control) (h : Path)
    (z : TestSpace levels ξ × TestSpace levels ξ) (hz : z ∈ graph levels ξ h) :
    (orderedDerivative levels ξ m hm T hT n controls z.1,
      orderedDerivative levels ξ m hm T hT n controls z.2) ∈ graph levels ξ h := by
  induction n generalizing z with
  | zero => exact hz
  | succ n ih =>
    exact ih _ _ (atControl_preserves_graph levels ξ m hm T hT (controls 0) h z hz)

theorem ordered_graph_step (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (controls : Fin n → Control) (q : TestSpace levels ξ) (u : Control) :
    (orderedDerivative levels ξ m hm T hT n controls (evolution levels ξ m hm T q),
      orderedDerivative levels ξ m hm T hT n controls (gradient levels ξ m hm T hT q u)) ∈
      graph levels ξ (direction u) :=
  ordered_preserves_graph levels ξ m hm T hT n controls (direction u) _
    (gradient_graph levels ξ m hm T hT q u)

end OperatorDerivativeRewrite.Foundation.FourierPathTimeTowers
