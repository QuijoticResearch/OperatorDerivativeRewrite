import Foundation.IBMSpatialFourthStep

/-! Actual bounded predictable spatial-Hilbert sums have a uniform fourth
moment bound. Every finite sum discharges its own integrability obligations. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSpatialFourthSums
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess IBMClockPastMoments
open IBMSpatialFourthStep

def sumProcess (τ : ℕ → ℝ≥0) (U : ℕ → SampleSpace → TimeHilbert) : ℕ → SampleSpace → TimeHilbert
  | 0 => fun _ => 0
  | n+1 => fun Y => sumProcess τ U n Y+delta (τ n) (τ (n+1)) Y • U n Y

theorem partial_past (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (U : ℕ → SampleSpace → TimeHilbert)
    (hU : ∀ j, StronglyMeasurable[naturalFiltration (τ j)] (U j)) (n : ℕ) :
    StronglyMeasurable[naturalFiltration (τ n)] (sumProcess τ U n) := by
  induction n with
  | zero => exact stronglyMeasurable_const
  | succ n ih =>
    have hab := hτ (Nat.le_succ n)
    exact (ih.mono (naturalFiltration.mono hab)).add
      (((process_stronglyAdapted (τ (n+1))).sub
        ((process_stronglyAdapted (τ n)).mono (naturalFiltration.mono hab))).smul
          ((hU n).mono (naturalFiltration.mono hab)))

theorem partial_memLp (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (κ : ℝ) (hκ : 0 ≤ κ)
    (U : ℕ → SampleSpace → TimeHilbert)
    (hU : ∀ j, StronglyMeasurable[naturalFiltration (τ j)] (U j))
    (hb : ∀ j Y, ‖U j Y‖ ≤ κ) (n : ℕ) : MemLp (sumProcess τ U n) 4 gaussianProduct := by
  induction n with
  | zero => exact memLp_const (0 : TimeHilbert)
  | succ n ih =>
    exact fourth_step_memLp (τ n) (τ (n+1)) (hτ (Nat.le_succ n)) κ hκ
      (sumProcess τ U n) (U n) (partial_past τ hτ U hU n) (hU n) ih (hb n)

theorem partial_moments (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (κ : ℝ) (hκ : 0 ≤ κ)
    (U : ℕ → SampleSpace → TimeHilbert)
    (hU : ∀ j, StronglyMeasurable[naturalFiltration (τ j)] (U j))
    (hb : ∀ j Y, ‖U j Y‖ ≤ κ) (n : ℕ) :
    (∫ Y, ‖sumProcess τ U n Y‖^2 ∂gaussianProduct) ≤ ((τ n : ℝ)-τ 0)*κ^2 ∧
      (∫ Y, ‖sumProcess τ U n Y‖^4 ∂gaussianProduct) ≤ 3*((τ n : ℝ)-τ 0)^2*κ^4 := by
  induction n with
  | zero => simp [sumProcess]
  | succ n ih =>
    have hab := hτ (Nat.le_succ n)
    have hdt : 0 ≤ (τ (n+1) : ℝ)-τ n := sub_nonneg.mpr (show (τ n : ℝ) ≤ τ (n+1) from hab)
    have hi := partial_memLp τ hτ κ hκ U hU hb n
    have h2 := second_step (τ n) (τ (n+1)) hab κ hκ
      (sumProcess τ U n) (U n) (partial_past τ hτ U hU n) (hU n) hi (hb n)
    have h4 := (fourth_step (τ n) (τ (n+1)) hab κ hκ
      (sumProcess τ U n) (U n) (partial_past τ hτ U hU n) (hU n) hi (hb n)).2
    constructor
    · change (∫ Y, ‖sumProcess τ U n Y+delta (τ n) (τ (n+1)) Y • U n Y‖^2
        ∂gaussianProduct) ≤ _
      calc
        _ ≤ (∫ Y, ‖sumProcess τ U n Y‖^2 ∂gaussianProduct)+((τ (n+1) : ℝ)-τ n)*κ^2 := h2
        _ ≤ ((τ (n+1) : ℝ)-τ 0)*κ^2 := by nlinarith [ih.1]
    · change (∫ Y, ‖sumProcess τ U n Y+delta (τ n) (τ (n+1)) Y • U n Y‖^4
        ∂gaussianProduct) ≤ _
      have hm := mul_le_mul_of_nonneg_left ih.1
        (by positivity : 0 ≤ 6*((τ (n+1) : ℝ)-τ n)*κ^2)
      nlinarith [ih.2]

theorem mollifier_partial_fourth (r : ℕ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n : ℕ) :
    (∫ Y, ‖sumProcess τ (fun j Y => IBMSpatialPointClockEnergy.spatial r (process (τ j) Y)) n Y‖^4
      ∂gaussianProduct) ≤ 3*((τ n : ℝ)-τ 0)^2*‖IBMPhysicalWhiteNoiseObstruction.profile r‖^4 := by
  exact (partial_moments τ hτ ‖IBMPhysicalWhiteNoiseObstruction.profile r‖ (norm_nonneg _)
    (fun j Y => IBMSpatialPointClockEnergy.spatial r (process (τ j) Y))
    (fun j => (IBMSpatialPointClockEnergy.spatial_stronglyMeasurable r).comp_measurable
      (process_stronglyAdapted (τ j)).measurable)
    (fun j Y => IBMSpatialPointClockEnergy.spatial_bound r (process (τ j) Y)) n).2

end OperatorDerivativeRewrite.Foundation.IBMSpatialFourthSums
