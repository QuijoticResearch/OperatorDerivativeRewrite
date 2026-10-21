import Foundation.HigherHeatAllChannelRemainder
import Foundation.HigherHeatQuadraticItoFields

/-! Actual signed power sums: every surviving channel and the drift converge in
completed-dual norm; all powers above the heat order vanish. Actual uniform
coefficient bounds and L1 field convergence are explicit. -/
noncomputable section
open scoped NNReal ENNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAllChannelLimit
open MeasureTheory Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain
open HigherHeatWeakTimeAdjoint HigherHeatDyadicStepAgreement HigherHeatAdaptedStepDuality
open HigherHeatCompletedPairing HigherHeatPairedDualCausality HigherHeatAllChannelNormalization
open HigherHeatAllPowerBounds HigherHeatAllChannelRemainder HigherHeatQuadraticItoFields

def powerPolynomial (n q : ℕ) (F : Fin (size n) → Test n) : Test n :=
  ∑ j, F j * (MvPolynomial.X j)^q

def remainder (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (r : ℕ) : Dual := ∑ j, cellRemainder n m hm T hT j (F j) r

theorem sum_identity (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) (r : ℕ) (hr : r < 2*m) :
    pairing m hm T hT (core (cylinderOf n (powerPolynomial n (r+1) F))) =
      remainder n m hm T hT F r + channel m T r (adaptedField n m hm T hT F) := by
  simp only [powerPolynomial, remainder, adaptedField, map_sum]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => power_step_split n m hm T hT j (F j)
    (adapted_missing hF j) r hr)

theorem remainder_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) (r : ℕ) (hr : r < 2*m) (M : ℝ)
    (hM : ∀ j, ‖pairing m hm T hT (core (cylinderOf n (F j)))‖ ≤ M) :
    ‖remainder n m hm T hT F r‖ ≤ powerConstant m T (r+1)*
      (HigherHeatDyadicLaws.duration 1 n:ℝ)*M := by
  calc
    _ ≤ ∑ j, ‖cellRemainder n m hm T hT j (F j) r‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (size n), powerConstant m T (r+1)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)^2*M := by
      apply Finset.sum_le_sum
      intro j _
      exact (cell_remainder_bound n m hm T hT j (F j) (adapted_missing hF j) r hr).trans
        (mul_le_mul_of_nonneg_left (hM j) (mul_nonneg (powerConstant_nonneg m T _) (sq_nonneg _)))
    _ = (size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
        (powerConstant m T (r+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*M) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by rw [HigherHeatQuadraticChannelLimit.size_duration]; ring

theorem remainder_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n))
    (r : ℕ) (hr : r < 2*m) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M) :
    Tendsto (fun n => remainder n m hm T hT (F n) r) atTop (𝓝 (0:Dual)) := by
  apply (tendsto_zero_iff_norm_tendsto_zero (E := Dual)).mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => remainder_bound n m hm T hT (F n) (hF n) r hr M (hM n))
  simpa using ((tendsto_const_nhds (x := powerConstant m T (r+1))).mul
    (HigherHeatEarlyDualContinuity.duration_tendsto 1)).mul (tendsto_const_nhds (x := M))

theorem power_sums_converge (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n))
    (r : ℕ) (hr : r < 2*m) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M)
    (A : Field timeMeasure)
    (hA : Tendsto (fun n => adaptedField n m hm T hT (F n)) atTop (𝓝 A)) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n (powerPolynomial n (r+1) (F n)))))
      atTop (𝓝 (channel m T r A)) := by
  let : ContinuousAdd Dual := (inferInstance : IsTopologicalAddGroup Dual).toContinuousAdd
  have hr' := remainder_tendsto m hm T hT F hF r hr M hM
  have hi := ((channel m T r).continuous.tendsto A).comp hA
  have hs := hr'.add hi
  have he : (fun n => remainder n m hm T hT (F n) r +
      channel m T r (adaptedField n m hm T hT (F n))) =
      (fun n => pairing m hm T hT (core (cylinderOf n (powerPolynomial n (r+1) (F n))))) :=
    funext (fun n => (sum_identity n m hm T hT (F n) (hF n) r hr).symm)
  change Tendsto (fun n => remainder n m hm T hT (F n) r +
    channel m T r (adaptedField n m hm T hT (F n))) atTop
      (𝓝 ((0:Dual)+channel m T r A)) at hs
  rw [he] at hs
  simpa only [zero_add] using hs

theorem higher_sum_bound (n m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : Fin (size n) → Test n) (hF : Adapted F) (r : ℕ) (hr : 2*m ≤ r) (M : ℝ)
    (hM : ∀ j, ‖pairing m hm T hT (core (cylinderOf n (F j)))‖ ≤ M) :
    ‖pairing m hm T hT (core (cylinderOf n (powerPolynomial n (r+1) F)))‖ ≤
      powerConstant m T (r+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*M := by
  simp only [powerPolynomial, map_sum]
  calc
    _ ≤ ∑ j, ‖pairing m hm T hT (core (cylinderOf n (F j*(MvPolynomial.X j)^(r+1))))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin (size n), powerConstant m T (r+1)*
        (HigherHeatDyadicLaws.duration 1 n:ℝ)^2*M := by
      apply Finset.sum_le_sum
      intro j _
      exact (higher_increment_bound n m hm T hT j (F j) (adapted_missing hF j) r hr).trans
        (mul_le_mul_of_nonneg_left (hM j) (mul_nonneg (powerConstant_nonneg m T _) (sq_nonneg _)))
    _ = (size n:ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*
        (powerConstant m T (r+1)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*M) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by rw [HigherHeatQuadraticChannelLimit.size_duration]; ring

theorem higher_sums_vanish (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (F : ∀ n, Fin (size n) → Test n) (hF : ∀ n, Adapted (F n))
    (r : ℕ) (hr : 2*m ≤ r) (M : ℝ)
    (hM : ∀ n j, ‖pairing m hm T hT (core (cylinderOf n (F n j)))‖ ≤ M) :
    Tendsto (fun n => pairing m hm T hT (core (cylinderOf n (powerPolynomial n (r+1) (F n)))))
      atTop (𝓝 (0:Dual)) := by
  apply (tendsto_zero_iff_norm_tendsto_zero (E := Dual)).mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => higher_sum_bound n m hm T hT (F n) (hF n) r hr M (hM n))
  simpa using ((tendsto_const_nhds (x := powerConstant m T (r+1))).mul
    (HigherHeatEarlyDualContinuity.duration_tendsto 1)).mul (tendsto_const_nhds (x := M))

theorem constant_sums_converge (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (r : ℕ) (hr : r < 2*m) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (powerPolynomial n (r+1) (fun _ => 1))))) atTop
        (𝓝 (channel m T r (constantField m hm T hT))) := by
  have hM (n : ℕ) (j : Fin (size n)) :
      ‖pairing m hm T hT (core (cylinderOf n (1:Test n)))‖ ≤
        ‖pairing m hm T hT (core (1:Cylinder))‖ := by rw [map_one]
  apply power_sums_converge m hm T hT (fun _ _ => 1)
    HigherHeatQuadraticItoData.constants_adapted r hr
    ‖pairing m hm T hT (core (1:Cylinder))‖ hM (constantField m hm T hT)
  simpa only [constants_field_eq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => constantField m hm T hT) atTop
      (𝓝 (constantField m hm T hT)))

theorem drift_constant (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    channel m T (2*m-1) (constantField m hm T hT) =
      (((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ)) • pairing m hm T hT (core (1:Cylinder)) := by
  rw [drift_normalization m hm T]
  apply ContinuousLinearMap.ext
  intro G
  change (((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ))*
    transpose timeMeasure 0 (constantField m hm T hT) G =
      (((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ))*pairing m hm T hT (core (1:Cylinder)) G
  congr 1
  rw [transpose_apply]
  calc
    _ = ∫ _t : ℝ, pairing m hm T hT (core (1:Cylinder)) G ∂timeMeasure := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [constantField_ae m hm T hT] with t ht
      rw [ht]
      rfl
    _ = _ := by simp [timeMeasure]

theorem constant_order_sums_converge (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) :
    Tendsto (fun n => pairing m hm T hT
      (core (cylinderOf n (powerPolynomial n (2*m) (fun _ => 1))))) atTop
        (𝓝 ((((2*m).factorial:ℝ)*(-1:ℝ)^(m+1)*(T:ℝ)) •
          pairing m hm T hT (core (1:Cylinder)))) := by
  have h := constant_sums_converge m hm T hT (2*m-1) (by omega)
  rw [show 2*m-1+1=2*m by omega, drift_constant m hm T hT] at h
  exact h

end OperatorDerivativeRewrite.Foundation.HigherHeatAllChannelLimit
