import Foundation.GaussianLipschitzIntegrands
import Mathlib.Analysis.Calculus.Taylor

/-! Actual second-order Taylor remainders and their Gaussian L2 estimates.
The stochastic moment estimate is derived from verified Hermite orthogonality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianTaylorRemainder
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeProcess GaussianTimeDivergence
open GaussianBrownianQuadraticVariation

/-- The remainder uses actual first and second derivatives of f. -/
def remainder (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  f y - f x - deriv f x * (y - x) - (1 / 2 : ℝ) * deriv (deriv f) x * (y - x) ^ 2

theorem remainder_bound (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (x y : ℝ) :
    ‖remainder f x y‖ ≤ (M / 6) * |y - x| ^ 3 := by
  by_cases hxy : x = y
  · subst y
    simp [remainder]
  obtain ⟨z, _, hz⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hxy hf.contDiffOn
  have hder (n : ℕ) (hn : n ≤ 3) :
      iteratedDerivWithin n f (uIcc x y) x = iteratedDeriv n f x :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hxy)
      (hf.of_le (by exact_mod_cast hn)).contDiffAt (left_mem_uIcc)
  have he : taylorWithinEval f 2 (uIcc x y) x y =
      f x + deriv f x * (y - x) + (1 / 2 : ℝ) * deriv (deriv f) x * (y - x) ^ 2 := by
    rw [taylorWithinEval_succ f 1, taylorWithinEval_succ f 0, taylor_within_zero_eval]
    rw [hder 1 (by decide), hder 2 (by decide)]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, smul_eq_mul]
    norm_num
    ring
  rw [he] at hz
  have hr : remainder f x y = iteratedDeriv 3 f z * (y - x) ^ 3 / 6 := by
    norm_num at hz
    dsimp only [remainder]
    linarith
  rw [hr, norm_div, norm_mul, norm_pow, Real.norm_eq_abs (y - x)]
  norm_num
  calc
    ‖iteratedDeriv 3 f z‖ * |y - x| ^ 3 / 6 ≤ M * |y - x| ^ 3 / 6 := by
      gcongr
      exact hM z
    _ = _ := by ring

def cube (h : CoefficientSpace) : GaussianL2 :=
  (wick h 3 : GaussianL2) + (3 * ‖h‖ ^ 2 : ℝ) • (wick h 1 : GaussianL2)

theorem cube_coeFn (h : CoefficientSpace) :
    cube h =ᵐ[gaussianProduct] fun ω => (firstChaosEmbedding h ω) ^ 3 := by
  filter_upwards [Lp.coeFn_add (wick h 3 : GaussianL2)
      ((3 * ‖h‖ ^ 2 : ℝ) • (wick h 1 : GaussianL2)),
    Lp.coeFn_smul (3 * ‖h‖ ^ 2 : ℝ) (wick h 1 : GaussianL2),
    core_coeFn h (‖h‖ ^ 2) 3, core_coeFn h (‖h‖ ^ 2) 1] with ω ha hs h3 h1
  change (cube h) ω = _
  rw [cube, ha]
  simp only [Pi.add_apply]
  rw [hs]
  change (core h (‖h‖ ^ 2) 3 : GaussianL2) ω +
    (3 * ‖h‖ ^ 2) * (core h (‖h‖ ^ 2) 1 : GaussianL2) ω = _
  rw [h3, h1, show (3 : ℕ) = 1 + 2 from rfl, value_recursion]
  simp only [value_two, value_one]
  norm_num
  ring

/-- The sixth moment is proved, not supplied as a Gaussian moment hypothesis. -/
theorem cube_norm_sq (h : CoefficientSpace) : ‖cube h‖ ^ 2 = 15 * (‖h‖ ^ 2) ^ 3 := by
  rw [cube, norm_add_sq_real, norm_smul, mul_pow, wick_norm_sq, wick_norm_sq,
    real_inner_smul_right, wick_inner]
  norm_num [Real.norm_eq_abs, sq_abs]
  ring

def incrementCube (s t : ℝ≥0) : GaussianL2 := cube (incrementDirection s t)

theorem incrementCube_coeFn (s t : ℝ≥0) (hst : s ≤ t) :
    incrementCube s t =ᵐ[gaussianProduct] fun ω => (process t ω - process s ω) ^ 3 := by
  filter_upwards [cube_coeFn (incrementDirection s t), process_increment_ae s t hst] with ω hc hi
  change firstChaosEmbedding (incrementDirection s t) ω = _ at hi
  exact hc.trans (congrArg (fun x : ℝ => x ^ 3) hi)

theorem incrementCube_norm_sq (s t : ℝ≥0) (hst : s ≤ t) :
    ‖incrementCube s t‖ ^ 2 = 15 * ((t : ℝ) - s) ^ 3 := by
  rw [incrementCube, cube_norm_sq, GaussianTimeFieldNorm.incrementDirection_norm_sq s t hst]

theorem remainder_measurable (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (s t : ℝ≥0) :
    Measurable (fun ω => remainder f (process s ω) (process t ω)) := by
  have h1 : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.continuous_iteratedDeriv 1 (by norm_num)
  have h2 : Continuous (deriv (deriv f)) := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      hf.continuous_iteratedDeriv 2 (by norm_num)
  exact (((hf.continuous.measurable.comp (process_stronglyMeasurable t).measurable).sub
    (hf.continuous.measurable.comp (process_stronglyMeasurable s).measurable)).sub
    ((h1.measurable.comp (process_stronglyMeasurable s).measurable).mul
      ((process_stronglyMeasurable t).measurable.sub (process_stronglyMeasurable s).measurable))).sub
    ((measurable_const.mul (h2.measurable.comp (process_stronglyMeasurable s).measurable)).mul
      (((process_stronglyMeasurable t).measurable.sub (process_stronglyMeasurable s).measurable).pow_const 2))

theorem remainder_memLp (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (s t : ℝ≥0) (hst : s ≤ t) :
    MemLp (fun ω => remainder f (process s ω) (process t ω)) 2 gaussianProduct := by
  apply (Lp.memLp (incrementCube s t)).of_le_mul
    (remainder_measurable f hf s t).aestronglyMeasurable (c := M / 6)
  filter_upwards [incrementCube_coeFn s t hst] with ω hc
  simpa only [hc, norm_pow, Real.norm_eq_abs] using remainder_bound f hf M hM (process s ω) (process t ω)

def remainderL2 (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (s t : ℝ≥0) (hst : s ≤ t) : GaussianL2 :=
  (remainder_memLp f hf M hM s t hst).toLp _

theorem remainderL2_coeFn (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (s t : ℝ≥0) (hst : s ≤ t) :
    remainderL2 f hf M hM s t hst =ᵐ[gaussianProduct]
      fun ω => remainder f (process s ω) (process t ω) := MemLp.coeFn_toLp _

theorem remainderL2_norm_sq (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (s t : ℝ≥0) (hst : s ≤ t) :
    ‖remainderL2 f hf M hM s t hst‖ ^ 2 ≤ (M / 6) ^ 2 * 15 * ((t : ℝ) - s) ^ 3 := by
  have hb : ‖remainderL2 f hf M hM s t hst‖ ≤ (M / 6) * ‖incrementCube s t‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [remainderL2_coeFn f hf M hM s t hst, incrementCube_coeFn s t hst] with ω hr hc
    simpa only [hr, hc, norm_pow, Real.norm_eq_abs] using
      remainder_bound f hf M hM (process s ω) (process t ω)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  simpa only [mul_pow, incrementCube_norm_sq s t hst, mul_assoc] using hs

theorem norm_sum_sq_le {n : ℕ} (v : Fin n → GaussianL2) :
    ‖∑ i, v i‖ ^ 2 ≤ (n : ℝ) * ∑ i, ‖v i‖ ^ 2 := by
  calc
    _ ≤ (∑ i, ‖v i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one] using
        Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) (fun i => ‖v i‖)

def remainderSum (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (T : ℝ≥0) (N : ℕ) : GaussianL2 :=
  ∑ i : Fin (N + 1), remainderL2 f hf M hM (uniformTime T N i.castSucc)
    (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i))

theorem remainderSum_coeFn (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (T : ℝ≥0) (N : ℕ) :
    remainderSum f hf M hM T N =ᵐ[gaussianProduct] fun ω =>
      ∑ i : Fin (N + 1), remainder f (process (uniformTime T N i.castSucc) ω)
        (process (uniformTime T N i.succ) ω) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N + 1) =>
    remainderL2 f hf M hM (uniformTime T N i.castSucc) (uniformTime T N i.succ)
      (uniformTime_monotone T N (Fin.castSucc_le_succ i))),
    ae_all_iff.mpr (fun i : Fin (N + 1) => remainderL2_coeFn f hf M hM
      (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i)))] with ω hs hi
  change remainderSum f hf M hM T N ω = _ at hs
  rw [hs]
  simp only [Finset.sum_apply, hi]

/-- An explicit bound for the sum, without independence of Taylor errors.
Cauchy--Schwarz for the finite sum retains the correct vanishing rate. -/
theorem remainderSum_norm_sq (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (T : ℝ≥0) (N : ℕ) :
    ‖remainderSum f hf M hM T N‖ ^ 2 ≤ (M / 6) ^ 2 * 15 * (T : ℝ) ^ 3 / (N + 1) := by
  calc
    _ ≤ (N + 1 : ℝ) * ∑ i : Fin (N + 1),
        ‖remainderL2 f hf M hM (uniformTime T N i.castSucc) (uniformTime T N i.succ)
          (uniformTime_monotone T N (Fin.castSucc_le_succ i))‖ ^ 2 := by
      simpa only [remainderSum, Nat.cast_add, Nat.cast_one] using norm_sum_sq_le
        (fun i : Fin (N + 1) => remainderL2 f hf M hM (uniformTime T N i.castSucc)
          (uniformTime T N i.succ) (uniformTime_monotone T N (Fin.castSucc_le_succ i)))
    _ ≤ (N + 1 : ℝ) * ∑ _i : Fin (N + 1), (M / 6) ^ 2 * 15 * ((T : ℝ) / (N + 1)) ^ 3 := by
      gcongr with i
      simpa only [uniformTime_step] using remainderL2_norm_sq f hf M hM
        (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      field_simp
      <;> ring

theorem remainderSum_tendsto (f : ℝ → ℝ) (hf : ContDiff ℝ 3 f) (M : ℝ)
    (hM : ∀ x, ‖iteratedDeriv 3 f x‖ ≤ M) (T : ℝ≥0) :
    Tendsto (remainderSum f hf M hM T) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => (M / 6) ^ 2 * 15 * (T : ℝ) ^ 3 / (N + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hn := squeeze_zero (fun N => sq_nonneg _) (remainderSum_norm_sq f hf M hM T) ht
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hn
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using hs

end OperatorDerivativeRewrite.Foundation.GaussianTaylorRemainder



