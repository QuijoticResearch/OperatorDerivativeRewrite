import Foundation.FourierPathTimeTowers
import Foundation.FourierPathControlTensors

/-! Genuine arbitrary-order Bochner time densities of native Frechet control tensors. -/
noncomputable section
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathTimeTensorIdentity
open HigherHeatDyadicLaws HigherHeatFourierBanach FourierPathBoundedControls
open BochnerControlTowers FourierPathTimeTowers FourierPathControlGradient FourierPathGradientCommutation
open HigherHeatFourierTranslations HigherHeatFourierPathSemigroup FourierPathSmoothControls

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

def total (n : ℕ) (T : ℝ≥0) : ℝ≥0 := (n:ℝ≥0)*T

theorem total_succ (n : ℕ) (T : ℝ≥0) : total (n+1) T = T+total n T := by
  unfold total
  push_cast
  ring

theorem ordered_snoc (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (controls : Fin (n+1) → Control) (q : TestSpace levels ξ) :
    orderedDerivative levels ξ m hm T hT (n+1) controls q =
      gradient levels ξ m hm T hT (orderedDerivative levels ξ m hm T hT n (Fin.init controls) q)
        (controls (Fin.last n)) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    change orderedDerivative levels ξ m hm T hT (n+1) (fun j => controls j.succ)
      (gradient levels ξ m hm T hT q (controls 0)) = _
    rw [ih]
    rfl

theorem fderiv_horizon (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (q : TestSpace levels ξ) :
    (fun u => fderiv ℝ (fun v => translation levels ξ (direction v)
      (evolution levels ξ m hm (total (n+1) T) q)) u) =
    (fun u => gradient levels ξ m hm T hT
      (translation levels ξ (direction u) (evolution levels ξ m hm (total n T) q))) := by
  have ht : 0 < total (n+1) T := by unfold total; positivity
  funext u
  rw [(FourierPathControlFrechet.orbit_hasFDerivAt levels ξ m hm _ ht q u).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  rw [← evolution_translation]
  simpa only [← total_succ] using
    (heat_split levels ξ m hm T hT (total n T) (translation levels ξ (direction u) q) v).symm

theorem tensor_eq_ordered (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (controls : Fin n → Control) (q : TestSpace levels ξ) :
    iteratedFDeriv ℝ n (fun v => translation levels ξ (direction v)
      (evolution levels ξ m hm (total n T) q)) 0 controls =
      orderedDerivative levels ξ m hm T hT n controls q := by
  induction n generalizing q with
  | zero =>
    rw [iteratedFDeriv_zero_apply]
    simp only [total, Nat.cast_zero, zero_mul, orderedDerivative, evolution_zero,
      FourierPathControlFrechet.direction_zero, translation_zero]
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      rw [iteratedFDeriv_one_apply]
      have he : total 1 T=T := by simp [total]
      rw [he, (FourierPathControlFrechet.orbit_hasFDerivAt levels ξ m hm T hT q 0).fderiv,
        FourierPathControlFrechet.direction_zero, translation_zero]
      rfl
    · have hn' : 0 < n := Nat.pos_of_ne_zero hn
      have ht : 0 < total n T := by unfold total; positivity
      rw [iteratedFDeriv_succ_apply_right, fderiv_horizon levels ξ m hm T hT n q]
      have hc := ((gradient levels ξ m hm T hT).restrictScalars ℝ).iteratedFDeriv_comp_left
        (x := (0:Control)) (orbit_contDiff_nat levels ξ m hm n (total n T) ht q).contDiffAt (i := n) le_rfl
      have he := congrArg (fun M => M (Fin.init controls) (controls (Fin.last n))) hc
      calc
        _ = gradient levels ξ m hm T hT
            (iteratedFDeriv ℝ n (fun v => translation levels ξ (direction v)
              (evolution levels ξ m hm (total n T) q)) 0 (Fin.init controls)) (controls (Fin.last n)) := he
        _ = gradient levels ξ m hm T hT
            (orderedDerivative levels ξ m hm T hT n (Fin.init controls) q) (controls (Fin.last n)) := by rw [ih]
        _ = _ := (ordered_snoc levels ξ m hm T hT n controls q).symm

theorem density_tensor (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (n : ℕ) (controls : Fin n → Control) (q : TestSpace levels ξ) :
    evaluate (base levels ξ) n controls (density levels ξ m hm T hT n q) =
      iteratedFDeriv ℝ n (fun v => translation levels ξ (direction v)
        (evolution levels ξ m hm (total n T) q)) 0 controls := by
  rw [density_pairing]
  exact (tensor_eq_ordered levels ξ m hm T hT n controls q).symm

def normalizedDensity (m : ℕ) (hm : 0 < m) (H : ℝ≥0) (hH : 0 < H)
    (n : ℕ) (hn : 0 < n) (q : TestSpace levels ξ) : tower (base levels ξ) n :=
  density levels ξ m hm (H/(n:ℝ≥0)) (div_pos hH (by exact_mod_cast hn)) n q

theorem normalized_pairing (m : ℕ) (hm : 0 < m) (H : ℝ≥0) (hH : 0 < H)
    (n : ℕ) (hn : 0 < n) (controls : Fin n → Control) (q : TestSpace levels ξ) :
    evaluate (base levels ξ) n controls (normalizedDensity levels ξ m hm H hH n hn q) =
      iteratedFDeriv ℝ n (fun v => translation levels ξ (direction v)
        (evolution levels ξ m hm H q)) 0 controls := by
  have hh := density_tensor levels ξ m hm (H/(n:ℝ≥0)) (div_pos hH (by exact_mod_cast hn)) n controls q
  have he : total n (H/(n:ℝ≥0))=H := by
    have hn0 : (n:ℝ≥0)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
    unfold total
    field_simp [hn0]
  rw [he] at hh
  exact hh

end OperatorDerivativeRewrite.Foundation.FourierPathTimeTensorIdentity
