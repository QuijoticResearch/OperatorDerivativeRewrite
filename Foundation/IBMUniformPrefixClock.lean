import Foundation.IBMUniformQuarticVariation

/-! Clock quadratic-variation errors on deterministic prefixes of one common
uniform grid. The prefix endpoint is allowed to vary with the grid size. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.IBMUniformPrefixClock
open InfiniteGaussian IBMConstructedSources IBMUniformClockGridEnergy
open GaussianBrownianQuadraticVariation
attribute [local irreducible] IBMConstructedSources.clockPath

def times (T : ℝ≥0) (n m : ℕ) : Fin (m + 1) → ℝ≥0 :=
  fun i => grid (T / (n + 1)) i.val

theorem times_monotone (T : ℝ≥0) (n m : ℕ) : Monotone (times T n m) := by
  intro i j hij
  unfold times grid
  gcongr
  exact hij

theorem times_step (T : ℝ≥0) (n m : ℕ) (i : Fin m) :
    (times T n m i.succ : ℝ) - times T n m i.castSucc = (T : ℝ) / (n + 1) := by
  simp only [times, grid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_add,
    NNReal.coe_one, NNReal.coe_natCast, Fin.val_succ, Fin.val_castSucc, Nat.cast_add,
    Nat.cast_one]
  ring

def error (T : ℝ≥0) (n m : ℕ) : GaussianL2 :=
  quadraticVariation (times T n m) - ((T : ℝ) / (n + 1) * m) • gaussianOne

theorem error_norm_sq (T : ℝ≥0) (n m : ℕ) :
    ‖error T n m‖ ^ 2 = 2 * m * ((T : ℝ) / (n + 1)) ^ 2 := by
  have he : ((times T n m (Fin.last m) : ℝ) - times T n m 0) =
      (T : ℝ) / (n + 1) * m := by simp [times, grid]
  have h := quadraticVariation_error_norm_sq (times T n m) (times_monotone T n m)
  rw [he] at h
  simpa only [error, times_step, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_assoc] using h

theorem error_norm_sq_le (T : ℝ≥0) (n m : ℕ) (hm : m ≤ n + 1) :
    ‖error T n m‖ ^ 2 ≤ 2 * (T : ℝ) ^ 2 / (n + 1) := by
  rw [error_norm_sq]
  have hp : 0 < (n + 1 : ℝ) := by positivity
  calc
    _ ≤ 2 * (n + 1 : ℝ) * ((T : ℝ) / (n + 1)) ^ 2 := by
      gcongr
      exact_mod_cast hm
    _ = _ := by field_simp

theorem error_tendsto (T : ℝ≥0) (m : ℕ → ℕ) (hm : ∀ n, m n ≤ n + 1) :
    Tendsto (fun n => error T n (m n)) atTop (𝓝 0) := by
  have hb : Tendsto (fun n : ℕ => 2 * (T : ℝ)^2 / (n + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hs := squeeze_zero (fun n => sq_nonneg ‖error T n (m n)‖)
    (fun n => error_norm_sq_le T n (m n) (hm n)) hb
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [sub_zero] using h

def actualError (T : ℝ≥0) (n m : ℕ) (ω : SampleSpace) : ℝ :=
  (∑ i ∈ Finset.range m,
    (clockPath ω (grid (T / (n + 1)) (i + 1)) - clockPath ω (grid (T / (n + 1)) i)) ^ 2) -
    (T : ℝ) / (n + 1) * m

theorem error_actual_ae (T : ℝ≥0) (n m : ℕ) :
    (error T n m : SampleSpace → ℝ) =ᵐ[gaussianProduct] actualError T n m := by
  have hc : ∀ᵐ ω ∂gaussianProduct, ∀ i : Fin (m + 1),
      clockPath ω (times T n m i) = GaussianTimeProcess.process (times T n m i) ω :=
    ae_all_iff.mpr fun i => clockPath_coordinate_ae _
  filter_upwards [Lp.coeFn_sub (quadraticVariation (times T n m))
      (((T : ℝ) / (n + 1) * m) • gaussianOne),
    Lp.coeFn_smul ((T : ℝ) / (n + 1) * m) gaussianOne, gaussianOne_coeFn,
    quadraticVariation_coeFn (times T n m) (times_monotone T n m), hc]
    with ω hsub hsm h1 hq hω
  change error T n m ω = _ at hsub
  rw [hsub]
  simp only [Pi.sub_apply, hq, hsm, Pi.smul_apply, h1, smul_eq_mul, mul_one]
  unfold actualError
  rw [Finset.sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← hω i.succ, ← hω i.castSucc]
  rfl

/-- The actual Brownian-clock prefix error tends to zero in probability,
with an independently proved Gaussian L2 bound uniform in deterministic m<=N. -/
theorem actualError_tendstoInMeasure (T : ℝ≥0) (m : ℕ → ℕ)
    (hm : ∀ n, m n ≤ n + 1) :
    TendstoInMeasure gaussianProduct (fun n => actualError T n (m n))
      atTop (fun _ => (0 : ℝ)) := by
  have h := tendstoInMeasure_of_tendsto_Lp (error_tendsto T m hm)
  exact h.congr (fun n => error_actual_ae T n (m n)) (Lp.coeFn_zero ℝ 2 gaussianProduct)

end OperatorDerivativeRewrite.Foundation.IBMUniformPrefixClock
