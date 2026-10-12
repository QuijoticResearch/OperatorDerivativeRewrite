import Foundation.GaussianQuadraticIncrement

/-! Actual Brownian squared-increment sums converge in Gaussian L2 on uniform
partitions. The exact error comes from Gaussian IBP, not an assumed bracket. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBrownianQuadraticVariation
open InfiniteGaussian GaussianTimeProcess GaussianTimeDivergence GaussianTimeFieldNorm
open GaussianQuadraticIncrement

theorem sum_fin_differences {n : ℕ} (a : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (a i.succ - a i.castSucc)) = a (Fin.last n) - a 0 := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ a
  have h₂ := Fin.sum_univ_castSucc a
  linarith

def quadraticVariation {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) : GaussianL2 :=
  ∑ i : Fin n, (incrementSquareError (τ i.castSucc) (τ i.succ) +
    ((τ i.succ : ℝ) - τ i.castSucc) • gaussianOne)

theorem quadraticVariation_coeFn {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    quadraticVariation τ =ᵐ[gaussianProduct] fun ω =>
      ∑ i : Fin n, (process (τ i.succ) ω - process (τ i.castSucc) ω) ^ 2 := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin n =>
    incrementSquareError (τ i.castSucc) (τ i.succ) +
      ((τ i.succ : ℝ) - τ i.castSucc) • gaussianOne),
    ae_all_iff.mpr (fun i : Fin n => Lp.coeFn_add
      (incrementSquareError (τ i.castSucc) (τ i.succ))
      (((τ i.succ : ℝ) - τ i.castSucc) • gaussianOne)),
    ae_all_iff.mpr (fun i : Fin n => Lp.coeFn_smul
      ((τ i.succ : ℝ) - τ i.castSucc) gaussianOne),
    ae_all_iff.mpr (fun i : Fin n => incrementSquareError_coeFn
      (τ i.castSucc) (τ i.succ) (hτ (Fin.castSucc_le_succ i))), gaussianOne_coeFn]
    with ω hsum hadd hsm he h1
  change quadraticVariation τ ω = _ at hsum
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hadd i]
  simp only [Pi.add_apply, he i, hsm i, Pi.smul_apply, h1, smul_eq_mul, mul_one,
    sub_add_cancel]

theorem quadraticVariation_error {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) :
    quadraticVariation τ - ((τ (Fin.last n) : ℝ) - τ 0) • gaussianOne =
      ∑ i : Fin n, incrementSquareError (τ i.castSucc) (τ i.succ) := by
  rw [quadraticVariation, Finset.sum_add_distrib, ← Finset.sum_smul,
    sum_fin_differences (fun i => (τ i : ℝ)),
    add_sub_cancel_right]

/-- Exact L2 error, valid also for repeated times and the empty partition. -/
theorem quadraticVariation_error_norm_sq {n : ℕ}
    (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ) :
    ‖quadraticVariation τ - ((τ (Fin.last n) : ℝ) - τ 0) • gaussianOne‖ ^ 2 =
      2 * ∑ i : Fin n, ((τ i.succ : ℝ) - τ i.castSucc) ^ 2 := by
  rw [quadraticVariation_error, ← real_inner_self_eq_norm_sq, sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq, incrementSquareError_norm_sq _ _
      (hτ (Fin.castSucc_le_succ i))]
  · intro j _ hji
    change inner ℝ (centeredSquare _ : GaussianL2) (centeredSquare _ : GaussianL2) = 0
    rw [centeredSquare_inner, partitionDirection_inner_eq_zero τ hτ i j hji.symm]
    norm_num
  · simp

def uniformTime (T : ℝ≥0) (n : ℕ) : Fin (n + 2) → ℝ≥0 :=
  fun i => T * (i : ℕ) / (n + 1 : ℕ)

theorem uniformTime_monotone (T : ℝ≥0) (n : ℕ) : Monotone (uniformTime T n) := by
  intro i j hij
  unfold uniformTime
  gcongr
  exact hij

theorem uniformTime_endpoints (T : ℝ≥0) (n : ℕ) :
    uniformTime T n 0 = 0 ∧ uniformTime T n (Fin.last (n + 1)) = T := by
  simp [uniformTime]

theorem uniformTime_step (T : ℝ≥0) (n : ℕ) (i : Fin (n + 1)) :
    (uniformTime T n i.succ : ℝ) - uniformTime T n i.castSucc = (T : ℝ) / (n + 1) := by
  simp only [uniformTime, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one, NNReal.coe_add, NNReal.coe_one]
  ring

theorem uniform_quadraticVariation_error (T : ℝ≥0) (n : ℕ) :
    ‖quadraticVariation (uniformTime T n) - (T : ℝ) • gaussianOne‖ ^ 2 =
      2 * (T : ℝ) ^ 2 / (n + 1) := by
  have h := quadraticVariation_error_norm_sq (uniformTime T n) (uniformTime_monotone T n)
  rw [(uniformTime_endpoints T n).1, (uniformTime_endpoints T n).2] at h
  simp only [NNReal.coe_zero, sub_zero, uniformTime_step, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  rw [h]
  field_simp

theorem uniform_quadraticVariation_tendsto (T : ℝ≥0) :
    Tendsto (fun n => quadraticVariation (uniformTime T n)) atTop
      (𝓝 ((T : ℝ) • gaussianOne)) := by
  have ht : Tendsto (fun n : ℕ => 2 * (T : ℝ) ^ 2 / (n + 1)) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp ht
  simp only [Real.sqrt_zero] at hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  convert hs using 1
  ext n
  simp only [Function.comp_apply]
  rw [← uniform_quadraticVariation_error, Real.sqrt_sq (norm_nonneg _)]

end OperatorDerivativeRewrite.Foundation.GaussianBrownianQuadraticVariation
