import Foundation.GaussianWeightedHermiteOrthogonality

/-! Weighted quadratic variation with arbitrary square-integrable raw-past coefficients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianWeightedQuadraticVariation
open InfiniteGaussian GaussianTimeProcess GaussianTimeSpaceHermite GaussianWeightedHermite
open GaussianWeightedHermiteOrthogonality GaussianBrownianQuadraticVariation
open GaussianPredictableStep (pastCoefficient)

variable {n : ℕ} (τ : Fin (n + 1) → ℝ≥0) (hτ : Monotone τ)
  (a : (i : Fin n) → (Iic (τ i.castSucc) → ℝ) → ℝ)
  (ha : ∀ i, Measurable (a i))
  (hA : ∀ i, MemLp (pastCoefficient process (τ i.castSucc) (a i)) 2 gaussianProduct)

def errorTerm (i : Fin n) : GaussianL2 :=
  coefficient (τ i.castSucc) (a i) (ha i) (hA i) (τ i.succ - τ i.castSucc) 2

def weightedError : GaussianL2 := ∑ i, errorTerm τ a ha hA i

include hτ

theorem errorTerm_coeFn (i : Fin n) :
    errorTerm τ a ha hA i =ᵐ[gaussianProduct] fun ω =>
      pastCoefficient process (τ i.castSucc) (a i) ω *
        ((process (τ i.succ) ω - process (τ i.castSucc) ω)^2 -
          ((τ i.succ : ℝ) - τ i.castSucc)) := by
  have hst := hτ (Fin.castSucc_le_succ i)
  have he := coefficient_coeFn (τ i.castSucc) (a i) (ha i) (hA i)
    (τ i.succ - τ i.castSucc) 2
  simpa only [errorTerm, add_tsub_cancel_of_le hst, value_two, NNReal.coe_sub hst] using he

theorem weightedError_coeFn : weightedError τ a ha hA =ᵐ[gaussianProduct] fun ω =>
    ∑ i, pastCoefficient process (τ i.castSucc) (a i) ω *
      ((process (τ i.succ) ω - process (τ i.castSucc) ω)^2 -
        ((τ i.succ : ℝ) - τ i.castSucc)) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (errorTerm τ a ha hA),
    ae_all_iff.mpr (errorTerm_coeFn τ hτ a ha hA)] with ω hs hi
  change (∑ i, errorTerm τ a ha hA i : GaussianL2) ω = _
  rw [hs]
  simp only [Finset.sum_apply, hi]

theorem errorTerm_norm_sq (i : Fin n) :
    ‖errorTerm τ a ha hA i‖^2 = 2 * ((τ i.succ : ℝ) - τ i.castSucc)^2 *
      ∫ ω, pastCoefficient process (τ i.castSucc) (a i) ω ^ 2 ∂gaussianProduct := by
  rw [errorTerm, coefficient_norm_sq, NNReal.coe_sub (hτ (Fin.castSucc_le_succ i))]
  norm_num
  ring

theorem errorTerm_inner_lt (i j : Fin n) (hij : i < j) :
    inner ℝ (errorTerm τ a ha hA i) (errorTerm τ a ha hA j) = 0 := by
  apply coefficient_inner_of_disjoint _ _ _ _ _ _ _ _ _ _ _ 2 1
  rw [add_tsub_cancel_of_le (hτ (Fin.castSucc_le_succ i))]
  exact hτ (Fin.succ_le_castSucc_iff.mpr hij)

theorem weightedError_norm_sq :
    ‖weightedError τ a ha hA‖^2 =
      2 * ∑ i, ((τ i.succ : ℝ) - τ i.castSucc)^2 *
        ∫ ω, pastCoefficient process (τ i.castSucc) (a i) ω ^ 2 ∂gaussianProduct := by
  rw [weightedError, ← real_inner_self_eq_norm_sq, sum_inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [real_inner_self_eq_norm_sq, errorTerm_norm_sq τ hτ a ha hA]
    ring
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with hj | hi
    · rw [real_inner_comm]
      exact errorTerm_inner_lt τ hτ a ha hA j i hj
    · exact errorTerm_inner_lt τ hτ a ha hA i j hi
  · simp

/-- An L2 bound on the coefficients suffices; essential boundedness is not required. -/
theorem weightedError_mesh_bound (M ε : ℝ) (hM : 0 ≤ M)
    (henergy : ∀ i, (∫ ω, pastCoefficient process (τ i.castSucc) (a i) ω ^ 2
      ∂gaussianProduct) ≤ M)
    (hmesh : ∀ i : Fin n, (τ i.succ : ℝ) - τ i.castSucc ≤ ε) :
    ‖weightedError τ a ha hA‖^2 ≤ 2 * M * ε * ((τ (Fin.last n) : ℝ) - τ 0) := by
  rw [weightedError_norm_sq τ hτ a ha hA]
  have hi (i : Fin n) : ((τ i.succ : ℝ) - τ i.castSucc)^2 *
      (∫ ω, pastCoefficient process (τ i.castSucc) (a i) ω ^ 2 ∂gaussianProduct) ≤
      M * ε * ((τ i.succ : ℝ) - τ i.castSucc) := by
    have hd : 0 ≤ (τ i.succ : ℝ) - τ i.castSucc := sub_nonneg.mpr (hτ (Fin.castSucc_le_succ i))
    calc
      _ ≤ ((τ i.succ : ℝ) - τ i.castSucc)^2 * M :=
        mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg _)
      _ ≤ M * ε * ((τ i.succ : ℝ) - τ i.castSucc) := by
        nlinarith [mul_nonneg hM (mul_nonneg hd (sub_nonneg.mpr (hmesh i)))]
  calc
    _ ≤ 2 * ∑ i, M * ε * ((τ i.succ : ℝ) - τ i.castSucc) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by norm_num)
    _ = _ := by rw [← Finset.mul_sum, sum_fin_differences (fun i => (τ i : ℝ))]; ring

omit hτ in
/-- Mesh convergence with a uniform second-moment bound; the weights may change with
the partition, and need not be bounded functions. -/
theorem weightedError_tendsto_of_mesh
    (m : ℕ → ℕ) (times : (N : ℕ) → Fin (m N + 1) → ℝ≥0)
    (htimes : ∀ N, Monotone (times N))
    (weights : (N : ℕ) → (i : Fin (m N)) → (Iic (times N i.castSucc) → ℝ) → ℝ)
    (hw : ∀ (N : ℕ) (i : Fin (m N)), Measurable (weights N i))
    (hw2 : ∀ (N : ℕ) (i : Fin (m N)), MemLp
      (pastCoefficient process (times N i.castSucc) (weights N i)) 2 gaussianProduct)
    (M L : ℝ) (hM : 0 ≤ M) (ε : ℕ → ℝ) (hε : ∀ N, 0 ≤ ε N)
    (hlim : Tendsto ε atTop (𝓝 0))
    (henergy : ∀ (N : ℕ) (i : Fin (m N)), (∫ ω, pastCoefficient process (times N i.castSucc) (weights N i) ω ^ 2
      ∂gaussianProduct) ≤ M)
    (hmesh : ∀ (N : ℕ) (i : Fin (m N)), (times N i.succ : ℝ) - times N i.castSucc ≤ ε N)
    (hlength : ∀ N, (times N (Fin.last (m N)) : ℝ) - times N 0 ≤ L) :
    Tendsto (fun N => weightedError (times N) (weights N) (hw N) (hw2 N)) atTop (𝓝 0) := by
  have hb (N : ℕ) : ‖weightedError (times N) (weights N) (hw N) (hw2 N)‖ ^ 2 ≤
      2 * M * ε N * L :=
    (weightedError_mesh_bound (times N) (htimes N) (weights N) (hw N) (hw2 N)
      M (ε N) hM (henergy N) (hmesh N)).trans
      (mul_le_mul_of_nonneg_left (hlength N)
        (mul_nonneg (mul_nonneg (by norm_num) hM) (hε N)))
  have hz : Tendsto (fun N => 2 * M * ε N * L) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (tendsto_const_nhds.mul hlim).mul_const L
  have hs := squeeze_zero (fun N => sq_nonneg _) hb hz
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hh

end OperatorDerivativeRewrite.Foundation.GaussianWeightedQuadraticVariation
