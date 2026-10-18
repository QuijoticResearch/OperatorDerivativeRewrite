import Foundation.IBMBoundaryVariance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Actual boundary covariance curvature of the Gaussian scenery convolution.
The boundary is kept in the variance formula, rather than inferred from a bulk
identity. No spatial Brownian local-time field is assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMBoundaryCurvature
open InfiniteGaussian IBMContinuousScenery IBMContinuousBulkVariance IBMBoundaryVariance

def negativeAverage (a b x : ℝ) (ρ : ℝ → ℝ) : ℝ :=
  ∫ r in Icc a b, ρ (-r) * max (-(x+r)) 0

theorem variance_decomposition (a b x : ℝ) {ρ : ℝ → ℝ} (hc : Continuous ρ)
    (hm : (∫ r in Icc a b, ρ (-r)) = 1) :
    ‖offsetScenery a b x ρ‖^2 = x + offsetCorrection a b ρ +
      2 * negativeAverage a b x ρ := by
  rw [offsetScenery_boundary_variance a b x hc]
  have hi (s : ℝ) :
      (∫ r in Icc a b, ρ (-r) *
        (x + min r s + max (-(x+r)) 0 + max (-(x+s)) 0)) =
      x + (∫ r in Icc a b, ρ (-r) * min r s) +
        negativeAverage a b x ρ + max (-(x+s)) 0 := by
    simp_rw [mul_add]
    rw [integral_add, integral_add, integral_add, integral_mul_const,
      integral_mul_const, hm, one_mul, one_mul]
    all_goals try rfl
    all_goals apply Continuous.integrableOn_Icc
    all_goals fun_prop
  have hcont : Continuous (fun s : ℝ => ∫ r in Icc a b, ρ (-r) * min r s) := by
    apply continuous_parametric_integral_of_continuous
    · fun_prop
    · exact isCompact_Icc
  simp_rw [hi, mul_add]
  rw [integral_add, integral_add, integral_add, integral_mul_const,
    integral_mul_const, hm]
  · unfold offsetCorrection negativeAverage
    ring
  all_goals apply Continuous.integrableOn_Icc
  all_goals fun_prop

def primitive (a x : ℝ) (ρ : ℝ → ℝ) : ℝ :=
  -x * (∫ r in a..-x, ρ (-r)) - ∫ r in a..-x, r * ρ (-r)

theorem negativeAverage_eq_primitive (a b x : ℝ) {ρ : ℝ → ℝ}
    (hc : Continuous ρ) (ha : a ≤ -x) (hb : -x ≤ b) :
    negativeAverage a b x ρ = primitive a x ρ := by
  have hcont : Continuous (fun r : ℝ => ρ (-r) * max (-(x+r)) 0) := by fun_prop
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) a (-x)) (hcont.intervalIntegrable (-x) b)
  rw [negativeAverage, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (ha.trans hb), ← hs]
  have hr : (∫ r in -x..b, ρ (-r) * max (-(x+r)) 0) = 0 := by
    rw [intervalIntegral.integral_of_le hb]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    rw [max_eq_right (by linarith [hr.1] : -(x+r) ≤ 0), mul_zero]
  rw [hr, add_zero, intervalIntegral.integral_of_le ha]
  have he : (∫ r in Ioc a (-x), ρ (-r) * max (-(x+r)) 0) =
      ∫ r in Ioc a (-x), (-x) * ρ (-r) - r * ρ (-r) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only
    rw [max_eq_left (by linarith [hr.2] : 0 ≤ -(x+r))]
    ring
  rw [he, integral_sub, integral_const_mul]
  · simp only [primitive, intervalIntegral.integral_of_le ha]
  all_goals apply Continuous.integrableOn_Ioc
  all_goals fun_prop

theorem primitive_hasDerivAt (a x : ℝ) {ρ : ℝ → ℝ} (hc : Continuous ρ) :
    HasDerivAt (fun y => primitive a y ρ)
      (-(∫ r in a..-x, ρ (-r))) x := by
  have h0 := (intervalIntegral.integral_hasDerivAt_right
    ((hc.comp continuous_neg).intervalIntegrable a (-x))
    ((hc.comp continuous_neg).stronglyMeasurableAtFilter volume _)
    (hc.comp continuous_neg).continuousAt).comp x (hasDerivAt_neg x)
  have h1c : Continuous (fun r : ℝ => r * ρ (-r)) := by fun_prop
  have h1 := (intervalIntegral.integral_hasDerivAt_right
    (h1c.intervalIntegrable a (-x)) (h1c.stronglyMeasurableAtFilter volume _)
    h1c.continuousAt).comp x (hasDerivAt_neg x)
  convert ((hasDerivAt_neg x).mul h0).sub h1 using 1 <;> (try funext y) <;>
    (try simp only [primitive, Function.comp_apply, Pi.sub_apply, Pi.mul_apply,
      neg_neg]) <;> ring

theorem negativeAverage_hasDerivAt (a b x : ℝ) {ρ : ℝ → ℝ}
    (hc : Continuous ρ) (ha : a < -x) (hb : -x < b) :
    HasDerivAt (fun y => negativeAverage a b y ρ)
      (-(∫ r in a..-x, ρ (-r))) x := by
  apply (primitive_hasDerivAt a x hc).congr_of_eventuallyEq
  filter_upwards [(continuous_neg.tendsto x).eventually
    (Ioo_mem_nhds ha hb)] with y hy
  exact negativeAverage_eq_primitive a b y hc hy.1.le hy.2.le

theorem offsetVariance_hasDerivAt (a b x : ℝ) {ρ : ℝ → ℝ}
    (hc : Continuous ρ) (hm : (∫ r in Icc a b, ρ (-r)) = 1)
    (ha : a < -x) (hb : -x < b) :
    HasDerivAt (fun y => ‖offsetScenery a b y ρ‖^2)
      (1 - 2 * (∫ r in a..-x, ρ (-r))) x := by
  have h := ((hasDerivAt_id x).add_const (offsetCorrection a b ρ)).add
    ((negativeAverage_hasDerivAt a b x hc ha hb).const_mul 2)
  have he : (fun y => ‖offsetScenery a b y ρ‖^2) =
      fun y => y + offsetCorrection a b ρ + 2 * negativeAverage a b y ρ :=
    funext fun y => variance_decomposition a b y hc hm
  rw [he]
  convert h using 1 <;> (try funext y) <;>
    (try simp only [Pi.add_apply, id_eq]) <;> ring

theorem offsetVariance_second_deriv (a b x : ℝ) {ρ : ℝ → ℝ}
    (hc : Continuous ρ) (hm : (∫ r in Icc a b, ρ (-r)) = 1)
    (ha : a < -x) (hb : -x < b) :
    deriv (fun y => deriv (fun z => ‖offsetScenery a b z ρ‖^2) y) x = 2 * ρ x := by
  have hi := (intervalIntegral.integral_hasDerivAt_right
    ((hc.comp continuous_neg).intervalIntegrable a (-x))
    ((hc.comp continuous_neg).stronglyMeasurableAtFilter volume _)
    (hc.comp continuous_neg).continuousAt).comp x (hasDerivAt_neg x)
  have hd : HasDerivAt (fun y => 1 - 2 * (∫ r in a..-y, ρ (-r))) (2 * ρ x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub (hi.const_mul 2) using 1 <;>
      (try funext y) <;> simp only [Function.comp_apply, Pi.sub_apply, neg_neg] <;> ring
  apply HasDerivAt.deriv
  apply hd.congr_of_eventuallyEq
  filter_upwards [(continuous_neg.tendsto x).eventually (Ioo_mem_nhds ha hb)] with y hy
  exact (offsetVariance_hasDerivAt a b y hc hm hy.1 hy.2).deriv

/-- Inside the actual boundary layer, the covariance bracket is the
normalized mollifier itself, not zero. -/
theorem concrete_covariance_bracket (n : ℕ) (x : ℝ)
    (hx : |x| < (IBMMollifier.bump n).rOut) :
    ‖wholeLineScenery (deriv (IBMMollifier.kernel n)) x‖^2 +
      inner ℝ (wholeLineScenery (IBMMollifier.kernel n) x)
        (wholeLineScenery (deriv (deriv (IBMMollifier.kernel n))) x) =
      IBMMollifier.kernel n x := by
  have hm : (∫ r in Icc (-(IBMMollifier.bump n).rOut) (IBMMollifier.bump n).rOut,
      IBMMollifier.kernel n (-r)) = 1 := by
    simpa using concreteMollifier_mass n 0
  have hs := offsetVariance_second_deriv (-(IBMMollifier.bump n).rOut)
    (IBMMollifier.bump n).rOut x (IBMMollifier.kernel_smooth n).continuous hm
    (by linarith [(abs_lt.mp hx).2]) (by linarith [(abs_lt.mp hx).1])
  have he : (fun z => ‖offsetScenery (-(IBMMollifier.bump n).rOut)
      (IBMMollifier.bump n).rOut z (IBMMollifier.kernel n)‖^2) =
      wholeLineVariance (IBMMollifier.kernel n) := by
    funext z
    rw [← IBMOffsetTranslation.concrete_wholeLineScenery_eq_offset]
    rfl
  rw [he, wholeLineVariance_second_deriv (IBMMollifier.kernel n)
    (IBMMollifier.kernel_compactSupport n)
    ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) x] at hs
  linarith

theorem kernel_even (n : ℕ) (r : ℝ) :
    IBMMollifier.kernel n (-r) = IBMMollifier.kernel n r :=
  (IBMMollifier.bump n).normed_neg r

/-- Exact one-sided boundary mass, including the factor required by reflection. -/
theorem kernel_half_mass (n : ℕ) :
    (∫ r in (0 : ℝ)..(IBMMollifier.bump n).rOut, IBMMollifier.kernel n r) = 1/2 := by
  let R := (IBMMollifier.bump n).rOut
  have hp : 0 ≤ R := (IBMMollifier.bump n).rOut_pos.le
  have hm := concreteMollifier_mass n 0
  simp only [zero_sub, zero_add] at hm
  simp_rw [kernel_even] at hm
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
    (show -R ≤ R by linarith)] at hm
  have hn := intervalIntegral.integral_comp_neg (f := IBMMollifier.kernel n)
    (a := (0 : ℝ)) (b := R)
  simp only [kernel_even, neg_zero] at hn
  have hs := intervalIntegral.integral_add_adjacent_intervals
    ((IBMMollifier.kernel_smooth n).continuous.intervalIntegrable
      (μ := volume) (-R) 0)
    ((IBMMollifier.kernel_smooth n).continuous.intervalIntegrable 0 R)
  change (∫ r in -R..R, IBMMollifier.kernel n r) = 1 at hm
  change (∫ r in (0 : ℝ)..R, IBMMollifier.kernel n r) = 1/2
  linarith

/-- The entire actual covariance bracket in the boundary layer has mass1/2.
This is a deterministic source identity, not yet F2's random clock limit. -/
theorem concrete_bracket_half_mass (n : ℕ) :
    (∫ x in Icc (0 : ℝ) (IBMMollifier.bump n).rOut,
      (‖wholeLineScenery (deriv (IBMMollifier.kernel n)) x‖^2 +
        inner ℝ (wholeLineScenery (IBMMollifier.kernel n) x)
          (wholeLineScenery (deriv (deriv (IBMMollifier.kernel n))) x))) = 1/2 := by
  rw [integral_Icc_eq_integral_Ioo]
  have he : (∫ x in Ioo (0 : ℝ) (IBMMollifier.bump n).rOut,
      (‖wholeLineScenery (deriv (IBMMollifier.kernel n)) x‖^2 +
        inner ℝ (wholeLineScenery (IBMMollifier.kernel n) x)
          (wholeLineScenery (deriv (deriv (IBMMollifier.kernel n))) x))) =
      ∫ x in Ioo (0 : ℝ) (IBMMollifier.bump n).rOut, IBMMollifier.kernel n x := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    exact concrete_covariance_bracket n x (by rw [abs_of_pos hx.1]; exact hx.2)
  rw [he, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (IBMMollifier.bump n).rOut_pos.le]
  exact kernel_half_mass n

theorem concrete_cross_covariance (n : ℕ) (x : ℝ)
    (hx : |x| < (IBMMollifier.bump n).rOut) :
    inner ℝ (wholeLineScenery (IBMMollifier.kernel n) x)
      (wholeLineScenery (deriv (IBMMollifier.kernel n)) x) =
      1/2 - ∫ r in (-(IBMMollifier.bump n).rOut)..-x,
        IBMMollifier.kernel n (-r) := by
  have hm : (∫ r in Icc (-(IBMMollifier.bump n).rOut) (IBMMollifier.bump n).rOut,
      IBMMollifier.kernel n (-r)) = 1 := by
    simpa using concreteMollifier_mass n 0
  have hs := (offsetVariance_hasDerivAt (-(IBMMollifier.bump n).rOut)
    (IBMMollifier.bump n).rOut x (IBMMollifier.kernel_smooth n).continuous hm
    (by linarith [(abs_lt.mp hx).2]) (by linarith [(abs_lt.mp hx).1])).deriv
  have he : (fun z => ‖offsetScenery (-(IBMMollifier.bump n).rOut)
      (IBMMollifier.bump n).rOut z (IBMMollifier.kernel n)‖^2) =
      wholeLineVariance (IBMMollifier.kernel n) := by
    funext z
    rw [← IBMOffsetTranslation.concrete_wholeLineScenery_eq_offset]
    rfl
  rw [he, wholeLineVariance_deriv (IBMMollifier.kernel n)
    (IBMMollifier.kernel_compactSupport n)
    ((IBMMollifier.kernel_smooth n).of_le (by norm_num)) x] at hs
  linarith

/-- The actual boundary Tanaka coefficient has zero scenery mean at the
origin, by covariance symmetry, not by a bulk substitution. -/
theorem concrete_cross_covariance_zero (n : ℕ) :
    inner ℝ (wholeLineScenery (IBMMollifier.kernel n) 0)
      (wholeLineScenery (deriv (IBMMollifier.kernel n)) 0) = 0 := by
  rw [concrete_cross_covariance n 0 (by simpa using (IBMMollifier.bump n).rOut_pos)]
  have hn := intervalIntegral.integral_comp_neg (f := IBMMollifier.kernel n)
    (a := -(IBMMollifier.bump n).rOut) (b := (0 : ℝ))
  simp only [neg_zero, neg_neg] at hn
  rw [neg_zero, hn, kernel_half_mass]
  norm_num

end OperatorDerivativeRewrite.Foundation.IBMBoundaryCurvature
