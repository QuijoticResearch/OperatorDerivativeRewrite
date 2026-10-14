import Foundation.PoissonDivergenceRecovery
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-! Finite-rank approximation and compactness of actual one-count Poisson recovery. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonRecoveryCompactness
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators
open PoissonCharlierHilbertBasis PoissonDivergenceRecovery

def partialRecovery (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) : ScalarL2 rate →L[ℝ] FieldL2 rate :=
  ∑ n∈Finset.range N, ((Real.sqrt (n+1 : ℝ))⁻¹ • innerSL ℝ (normalized rate hr (n+1))).smulRight
    (normalizedField rate hr n)

theorem partialRecovery_apply (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) (f : ScalarL2 rate) :
    partialRecovery rate hr N f=∑ n∈Finset.range N, inverseCoefficient rate hr f n • normalizedField rate hr n := by
  simp only [partialRecovery,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro n hn
  change ((Real.sqrt (n+1 : ℝ))⁻¹*inner ℝ (normalized rate hr (n+1)) f) • normalizedField rate hr n=_
  rw [inverseCoefficient,PoissonDivergenceRecovery.coefficient,div_eq_mul_inv,mul_comm]

theorem partialRecovery_compact (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) :
    IsCompactOperator (partialRecovery rate hr N) := by
  have hterm (n : ℕ) : IsCompactOperator
      (((Real.sqrt (n+1 : ℝ))⁻¹ • innerSL ℝ (normalized rate hr (n+1))).smulRight (normalizedField rate hr n)) := by
    have hc := isCompactOperator_of_locallyCompactSpace_rng
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (normalizedField rate hr n))
    exact hc.comp_clm ((Real.sqrt (n+1 : ℝ))⁻¹ • innerSL ℝ (normalized rate hr (n+1)))
  unfold partialRecovery
  induction Finset.range N using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      change IsCompactOperator (0 : ScalarL2 rate → FieldL2 rate)
      exact isCompactOperator_zero
  | @insert n s hn ih =>
      rw [Finset.sum_insert hn]
      change IsCompactOperator (fun f : ScalarL2 rate =>
        (((Real.sqrt (n+1 : ℝ))⁻¹ • innerSL ℝ (normalized rate hr (n+1))).smulRight (normalizedField rate hr n)) f+
        (∑ j∈s, ((Real.sqrt (j+1 : ℝ))⁻¹ • innerSL ℝ (normalized rate hr (j+1))).smulRight (normalizedField rate hr j)) f)
      exact (hterm n).add ih

def tailCoefficient (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) (f : ScalarL2 rate) (n : ℕ) : ℝ :=
  if n<N then 0 else inverseCoefficient rate hr f n

theorem recovery_tail_hasSum (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) (f : ScalarL2 rate) :
    HasSum (fun n => tailCoefficient rate hr N f n • normalizedField rate hr n)
      (recovery rate hr f-partialRecovery rate hr N f) := by
  have hp : HasSum (fun n => if n∈Finset.range N then inverseCoefficient rate hr f n • normalizedField rate hr n else 0)
      (partialRecovery rate hr N f) := by
    have ht := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) (s := Finset.range N)
      (f := fun n => if n∈Finset.range N then inverseCoefficient rate hr f n • normalizedField rate hr n else 0)
      (fun n hn => by simp [hn])
    simpa only [Finset.sum_ite_mem,Finset.inter_self,partialRecovery_apply] using ht
  have ht := (recovery_summable rate hr f).hasSum.sub hp
  have he (n : ℕ) : inverseCoefficient rate hr f n • normalizedField rate hr n-
      (if n∈Finset.range N then inverseCoefficient rate hr f n • normalizedField rate hr n else 0)=
        tailCoefficient rate hr N f n • normalizedField rate hr n := by
    by_cases hn : n<N <;> simp [tailCoefficient,Finset.mem_range,hn]
  simpa only [he,recovery] using ht

theorem recovery_tail_energy (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) (f : ScalarL2 rate) :
    HasSum (fun n => (tailCoefficient rate hr N f n)^2) (‖recovery rate hr f-partialRecovery rate hr N f‖^2) := by
  have ht := (recovery_tail_hasSum rate hr N f).norm.pow 2
  change Tendsto (fun s : Finset ℕ => ‖∑ n∈s, tailCoefficient rate hr N f n • normalizedField rate hr n‖^2)
    atTop (𝓝 (‖recovery rate hr f-partialRecovery rate hr N f‖^2)) at ht
  change Tendsto (fun s : Finset ℕ => ∑ n∈s, (tailCoefficient rate hr N f n)^2)
    atTop (𝓝 (‖recovery rate hr f-partialRecovery rate hr N f‖^2))
  have he (s : Finset ℕ) : ‖∑ n∈s, tailCoefficient rate hr N f n • normalizedField rate hr n‖^2=
      ∑ n∈s, (tailCoefficient rate hr N f n)^2 := by
    simpa only [LinearIsometry.toSpanSingleton_apply,Real.norm_eq_abs,sq_abs] using
      (normalizedField_orthonormal rate hr).orthogonalFamily.norm_sum (tailCoefficient rate hr N f) s
  simpa only [he] using ht

theorem tailCoefficient_sq_bound (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) (f : ScalarL2 rate) (n : ℕ) :
    (tailCoefficient rate hr N f n)^2≤(N+1 : ℝ)⁻¹*(PoissonDivergenceRecovery.coefficient rate hr f (n+1))^2 := by
  by_cases hn : n<N
  · simp only [tailCoefficient,if_pos hn,zero_pow (by norm_num : (2 : ℕ)≠0)]
    positivity
  · rw [tailCoefficient,if_neg hn,inverseCoefficient,div_pow,Real.sq_sqrt (by positivity)]
    rw [mul_comm,← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    exact_mod_cast (show N+1≤n+1 by omega)

theorem recovery_tail_bound (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) (f : ScalarL2 rate) :
    ‖recovery rate hr f-partialRecovery rate hr N f‖^2≤(N+1 : ℝ)⁻¹*‖f‖^2 := by
  have hc := (coefficient_energy rate hr f).summable.comp_injective
    (fun a b (h : a+1=b+1) => Nat.add_right_cancel h)
  have he := hasSum_le (tailCoefficient_sq_bound rate hr N f) (recovery_tail_energy rate hr N f)
    (hc.hasSum.mul_left ((N+1 : ℝ)⁻¹))
  have hb : (∑' n, (PoissonDivergenceRecovery.coefficient rate hr f (n+1))^2)≤‖f‖^2 := by
    rw [← (coefficient_energy rate hr f).tsum_eq]
    exact hc.tsum_le_tsum_of_inj (fun n => n+1) (fun _ _ h => Nat.add_right_cancel h)
      (fun _ _ => sq_nonneg _) (fun _ => le_rfl) (coefficient_energy rate hr f).summable
  simpa only [Function.comp_apply] using he.trans (mul_le_mul_of_nonneg_left hb (by positivity))

theorem recovery_tail_operator_bound (rate : ℝ≥0) (hr : 0<rate) (N : ℕ) :
    ‖recoveryOperator rate hr-partialRecovery rate hr N‖≤Real.sqrt ((N+1 : ℝ)⁻¹) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro f
  change ‖recovery rate hr f-partialRecovery rate hr N f‖≤Real.sqrt ((N+1 : ℝ)⁻¹)*‖f‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (by positivity)]
  exact recovery_tail_bound rate hr N f

theorem partialRecovery_tendsto (rate : ℝ≥0) (hr : 0<rate) :
    Tendsto (partialRecovery rate hr) atTop (𝓝 (recoveryOperator rate hr)) := by
  have hn : Tendsto (fun N : ℕ => (N+1 : ℝ)) atTop atTop := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hi := tendsto_inv_atTop_zero.comp hn
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hi
  have hs0 : Tendsto (fun N : ℕ => Real.sqrt ((N+1 : ℝ)⁻¹)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun N => norm_nonneg _) _ hs0
  intro N
  rw [norm_sub_rev]
  exact recovery_tail_operator_bound rate hr N

theorem recovery_compact (rate : ℝ≥0) (hr : 0<rate) : IsCompactOperator (recoveryOperator rate hr) :=
  isCompactOperator_of_tendsto (partialRecovery_tendsto rate hr)
    (Eventually.of_forall (partialRecovery_compact rate hr))
end OperatorDerivativeRewrite.Foundation.PoissonRecoveryCompactness





