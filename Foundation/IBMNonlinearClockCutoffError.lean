import Foundation.IBMNonlinearClockTailEnergy

/-! Actual original nonlinear clock average minus its bounded spatial cutoff.
The uniform full-vector error estimate requires a cutoff equal to one on a
specified symmetric interval. No product-observable derivative is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNonlinearClockCutoffError
open InfiniteGaussian IBMConstructedSources IBMNonlinearClockTailEnergy
open IBMClockOverlapEnergy IBMFoldedTransitionBound

theorem complement_le_tail (χ : ℝ → ℝ) (h0 : ∀ x, 0 ≤ χ x)
    (R : ℝ) (hcore : ∀ x, |x| ≤ R → χ x = 1) (x : ℝ) :
    1 - χ x ≤ IBMClockTailOverlap.tail R x := by
  by_cases hx : R < |x|
  · simp only [IBMClockTailOverlap.tail,ite_eq_left hx]
    linarith [h0 x]
  · rw [hcore x (le_of_not_gt hx)]
    simp only [sub_self]
    exact IBMClockTailOverlap.tail_nonneg R x

theorem field_complement_eq (χ : ℝ → ℝ) (hχ : Measurable χ)
    (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (n : ℕ) (t : ℝ) :
    field (fun x => 1-χ x) n t = IBMNonlinearClockField.field n t - field χ n t := by
  have hc0 (x : ℝ) : 0 ≤ 1-χ x := sub_nonneg.mpr (h1 x)
  have hc1 (x : ℝ) : 1-χ x ≤ 1 := by linarith [h0 x]
  apply Lp.ext
  filter_upwards [field_ae (fun x => 1-χ x) (measurable_const.sub hχ) hc0 hc1 n t,
    field_ae χ hχ h0 h1 n t,IBMNonlinearClockField.field_ae n t,
    Lp.coeFn_sub (IBMNonlinearClockField.field n t) (field χ n t)] with Y hc hcut hold hsub
  rw [hc,hsub,Pi.sub_apply,hold,hcut,maskedSection,maskedSection,sub_smul,one_smul]

theorem average_complement_eq (χ : ℝ → ℝ) (hχ : Measurable χ)
    (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    average (fun x => 1-χ x) n T = IBMNonlinearClockEnergy.average n T - average χ n T := by
  unfold IBMNonlinearClockTailEnergy.average IBMNonlinearClockEnergy.average
  simp_rw [field_complement_eq χ hχ h0 h1]
  exact integral_sub (IBMNonlinearClockField.field_integrable n hT)
    (field_integrable χ hχ h0 h1 n hT)

/-- The norm is the FULL clock/source/coefficient Bochner-L2 norm of the
actual native averaged fields, uniformly in the smoothing width n. -/
theorem average_cutoff_error (χ : ℝ → ℝ) (hχ : Measurable χ)
    (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) {R : ℝ} (hR : 0 < R)
    (hcore : ∀ x, |x| ≤ R → χ x = 1) (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖IBMNonlinearClockEnergy.average n T - average χ n T‖^2 ≤
      (T/R^2) * (8*peak 1*T^2*Real.sqrt T+4*T^3) := by
  rw [← average_complement_eq χ hχ h0 h1 n hT]
  exact average_uniform_tail_energy _ (measurable_const.sub hχ)
    (fun x => sub_nonneg.mpr (h1 x)) hR (complement_le_tail χ h0 R hcore) n hT

/-- Radii growing as j+1 remove the full-vector cutoff error even if the
smoothing width n(j) changes arbitrarily at the same time. -/
theorem cutoff_error_tendsto (χ : ℕ → ℝ → ℝ) (hχ : ∀ j, Measurable (χ j))
    (h0 : ∀ j x, 0 ≤ χ j x) (h1 : ∀ j x, χ j x ≤ 1)
    (hcore : ∀ (j : ℕ) (x : ℝ), |x| ≤ (j : ℝ) + 1 → χ j x = 1)
    (n : ℕ → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun j => ‖IBMNonlinearClockEnergy.average (n j) T - average (χ j) (n j) T‖)
      atTop (𝓝 0) := by
  let C := 8*peak 1*T^2*Real.sqrt T+4*T^3
  have ht := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hb : Tendsto (fun j : ℕ => (T/((j : ℝ) + 1)^2)*C) atTop (𝓝 0) := by
    convert ((tendsto_const_nhds (x := T)).mul (ht.pow 2)).mul_const C using 1
    · congr 1
      funext j
      simp only [div_eq_mul_inv,one_mul,inv_pow]
    · simp
  have hs := squeeze_zero' (Eventually.of_forall fun j => sq_nonneg
    ‖IBMNonlinearClockEnergy.average (n j) T - average (χ j) (n j) T‖)
    (Eventually.of_forall fun j => average_cutoff_error (χ j) (hχ j) (h0 j) (h1 j)
      (by positivity : (0:ℝ)<(j : ℝ) + 1) (hcore j) (n j) hT) hb
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hr

def cutoff (j : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (j : ℝ) + 1
  rOut := 2*((j : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j; linarith

theorem cutoff_continuous (j : ℕ) : Continuous (cutoff j) := (cutoff j).continuous

theorem cutoff_compactSupport (j : ℕ) : HasCompactSupport (cutoff j) :=
  (cutoff j).hasCompactSupport

theorem cutoff_one (j : ℕ) (x : ℝ) (hx : |x| ≤ (j : ℝ) + 1) : cutoff j x = 1 := by
  apply (cutoff j).one_of_mem_closedBall
  simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero,cutoff] using hx

theorem native_cutoff_error_tendsto (n : ℕ → ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Tendsto (fun j => ‖IBMNonlinearClockEnergy.average (n j) T -
      average (cutoff j) (n j) T‖) atTop (𝓝 0) :=
  cutoff_error_tendsto (fun j => cutoff j) (fun j => (cutoff_continuous j).measurable)
    (fun j x => (cutoff j).nonneg' x) (fun j x => (cutoff j).le_one (x := x)) cutoff_one n hT

end OperatorDerivativeRewrite.Foundation.IBMNonlinearClockCutoffError
