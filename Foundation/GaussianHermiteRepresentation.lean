import Foundation.GaussianHermiteStochasticSums
import Foundation.GaussianBrownianQuadraticVariation
import Foundation.GaussianBrownianGeneratedSpace
import Mathlib.Algebra.Ring.GeomSum

/-! Genuine L2 convergence of all-order Hermite stochastic sums. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianHermiteRepresentation
open InfiniteGaussian GaussianTimeSpaceHermite GaussianHermiteStochasticSums
open GaussianBrownianQuadraticVariation GaussianPredictableFull GaussianPredictableAdjoint

theorem power_increment_upper (n : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    b ^ (n + 1) - a ^ (n + 1) ≤ (n + 1 : ℝ) * b ^ n * (b - a) := by
  have hs : (∑ i ∈ Finset.range (n + 1), b ^ i * a ^ (n - i)) ≤ (n + 1 : ℝ) * b ^ n := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), b ^ n := by
        apply Finset.sum_le_sum
        intro i hi
        have hil : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        calc
          _ ≤ b ^ i * b ^ (n - i) := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ ha hab _) (pow_nonneg (ha.trans hab) _)
          _ = b ^ n := by rw [← pow_add, Nat.add_sub_of_le hil]
      _ = _ := by simp
  have hg := (Commute.all b a).geom_sum₂_mul (n + 1)
  simp only [Nat.add_sub_cancel] at hg
  rw [← hg]
  exact mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hab)

theorem uniform_power_error_upper (n N : ℕ) (T : ℝ≥0) :
    (T : ℝ) ^ (n + 1) - (n + 1 : ℝ) *
      ∑ i : Fin (N + 1),
        ((uniformTime T N i.succ : ℝ) - uniformTime T N i.castSucc) *
          (uniformTime T N i.castSucc : ℝ) ^ n ≤
      (n + 1 : ℝ) * ((T : ℝ) / (N + 1)) * (T : ℝ) ^ n := by
  let τ := uniformTime T N
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin (N + 1)) _ =>
    power_increment_upper n (NNReal.coe_nonneg (τ i.castSucc))
      (show (τ i.castSucc : ℝ) ≤ τ i.succ from uniformTime_monotone T N (Fin.castSucc_le_succ i)))
  rw [sum_fin_differences (fun i : Fin (N + 2) => (τ i : ℝ) ^ (n + 1))] at hs
  change (τ (Fin.last (N + 1)) : ℝ) ^ (n + 1) - (τ 0 : ℝ) ^ (n + 1) ≤ _ at hs
  simp only [τ, (uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2,
    NNReal.coe_zero, zero_pow (Nat.succ_ne_zero n), sub_zero, uniformTime_step] at hs
  have hd := sum_fin_differences (fun i : Fin (N + 2) => (τ i : ℝ) ^ n)
  simp only [τ, (uniformTime_endpoints T N).1, (uniformTime_endpoints T N).2, NNReal.coe_zero] at hd
  rw [Finset.sum_sub_distrib] at hd
  simp only [uniformTime_step]
  have he : (∑ i : Fin (N + 1), (n + 1 : ℝ) * (uniformTime T N i.succ : ℝ) ^ n *
      ((T : ℝ) / (N + 1))) = (n + 1 : ℝ) * ((T : ℝ) / (N + 1)) *
        ∑ i : Fin (N + 1), (uniformTime T N i.succ : ℝ) ^ n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hs
  rw [← Finset.mul_sum]
  have hz : 0 ≤ (n + 1 : ℝ) * ((T : ℝ) / (N + 1)) * (0 : ℝ) ^ n := by positivity
  have hd' := congrArg (fun z : ℝ => ((n + 1 : ℝ) * ((T : ℝ) / (N + 1))) * z) hd
  nlinarith [hd']

theorem uniform_stochasticSum_error_bound (n N : ℕ) (T : ℝ≥0) :
    ‖(brownianCore T (n + 1) : GaussianL2) -
      (n + 1 : ℝ) • itoIntegral (stepSum n (uniformTime T N))‖ ^ 2 ≤
        ((n + 1).factorial : ℝ) * (n + 1 : ℝ) * (T : ℝ) ^ (n + 1) / (N + 1) := by
  have he := stochasticSum_error n (uniformTime T N) (uniformTime_monotone T N)
  rw [(uniformTime_endpoints T N).2] at he
  rw [he]
  calc
    _ ≤ ((n + 1).factorial : ℝ) * ((n + 1 : ℝ) * ((T : ℝ) / (N + 1)) * (T : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left (uniform_power_error_upper n N T) (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem scaled_stochasticSum_tendsto (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => (n + 1 : ℝ) • itoIntegral (stepSum n (uniformTime T N))) atTop
      (𝓝 (brownianCore T (n + 1) : GaussianL2)) := by
  have ht : Tendsto (fun N : ℕ => ((n + 1).factorial : ℝ) * (n + 1 : ℝ) *
      (T : ℝ) ^ (n + 1) / (N + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hs := squeeze_zero (fun N => sq_nonneg _)
    (fun N => uniform_stochasticSum_error_bound n N T) ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_sub_rev] using hh

theorem stochasticSum_tendsto (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => itoIntegral (stepSum n (uniformTime T N))) atTop
      (𝓝 ((n + 1 : ℝ)⁻¹ • (brownianCore T (n + 1) : GaussianL2))) := by
  have h := (scaled_stochasticSum_tendsto n T).const_smul (n + 1 : ℝ)⁻¹
  simpa only [smul_smul, inv_mul_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0), one_smul] using h

theorem hermite_mem_integralRange (n : ℕ) (T : ℝ≥0) :
    (n + 1 : ℝ)⁻¹ • (brownianCore T (n + 1) : GaussianL2) ∈ itoIntegral.toLinearMap.range :=
  GaussianBrownianGeneratedSpace.integralRange_isClosed.mem_of_tendsto
    (stochasticSum_tendsto n T) (Eventually.of_forall fun N => ⟨stepSum n (uniformTime T N), rfl⟩)

def hermiteIntegrand (n : ℕ) (T : ℝ≥0) : fullPredictable :=
  predictableAdjoint ((n + 1 : ℝ)⁻¹ • (brownianCore T (n + 1) : GaussianL2))

theorem integral_hermiteIntegrand (n : ℕ) (T : ℝ≥0) :
    itoIntegral (hermiteIntegrand n T) = (n + 1 : ℝ)⁻¹ • (brownianCore T (n + 1) : GaussianL2) := by
  obtain ⟨u, hu⟩ := hermite_mem_integralRange n T
  change itoIntegral u = _ at hu
  unfold hermiteIntegrand
  rw [← hu, predictableAdjoint_integral]

theorem hermite_representation (n : ℕ) (T : ℝ≥0) :
    (brownianCore T (n + 1) : GaussianL2) = (n + 1 : ℝ) • itoIntegral (hermiteIntegrand n T) := by
  rw [integral_hermiteIntegrand, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]

theorem stepSum_tendsto (n : ℕ) (T : ℝ≥0) :
    Tendsto (fun N => stepSum n (uniformTime T N)) atTop (𝓝 (hermiteIntegrand n T)) := by
  have h := predictableAdjoint.continuous.continuousAt.tendsto.comp (stochasticSum_tendsto n T)
  simpa only [Function.comp_def, predictableAdjoint_integral, hermiteIntegrand] using h

end OperatorDerivativeRewrite.Foundation.GaussianHermiteRepresentation
