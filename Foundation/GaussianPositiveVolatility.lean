import Foundation.GaussianSensitivityCore
import Foundation.GaussianDeterministicVolterra

/-! A strictly positive, genuinely random polynomial volatility example.
It is not bounded: the active coefficient is 1+B_a^2. All moments and the
actual closed derivative follow from genuine polynomial differentiation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPositiveVolatility
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProcess GaussianTimeDivergence
open GaussianTimeSensitivity GaussianTimePolynomialPairing GaussianTimeFieldNorm
open GaussianTimeProductL2 GaussianPredictableFull GaussianSensitivityCore
open GaussianContinuousRigidity GaussianProductDerivative SeparableHilbertEmbedding
attribute [local instance] timeHilbert_secondCountable

def polynomial : MvPolynomial (Fin 1) ℝ := 1 + (X 0)^2

def delayedField (a b : ℝ≥0) : fullPredictable :=
  pastStep a b (fun _ : Fin 1 => a) (fun _ => le_rfl) polynomial

theorem coefficient_coeFn (a : ℝ≥0) :
    (pastCoefficient (fun _ : Fin 1 => a) polynomial : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => 1 + process a ω ^ 2 := by
  simpa [polynomial] using pastCoefficient_coeFn (fun _ : Fin 1 => a) polynomial

theorem coefficient_positive (a : ℝ≥0) :
    ∀ᵐ ω ∂gaussianProduct,
      1 ≤ (pastCoefficient (fun _ : Fin 1 => a) polynomial : GaussianL2) ω := by
  filter_upwards [coefficient_coeFn a] with ω hω
  rw [hω]
  linarith [sq_nonneg (process a ω)]

theorem delayedField_sobolev (a b : ℝ≥0) :
    (delayedField a b : TimeProbabilityL2) ∈ predictableSobolev :=
  past_polynomial_step_mem_predictableSobolev a b (fun _ : Fin 1 => a) (fun _ => le_rfl) polynomial

theorem delayed_integral_coeFn (a b : ℝ≥0) (hab : a ≤ b) :
    itoIntegral (delayedField a b) =ᵐ[gaussianProduct]
      fun ω => (1 + process a ω ^ 2) * (process b ω - process a ω) := by
  rw [delayedField, ito_pastStep a b hab]
  simpa [polynomial] using incrementProductL2_coeFn (fun _ : Fin 1 => a) polynomial a b

theorem coefficient_derivative (a : ℝ≥0) :
    polynomialDerivative (pastCoefficient (fun _ : Fin 1 => a) polynomial) =ᵐ[gaussianProduct]
      fun ω => (2 * process a ω) • hilbertEmbedding TimeHilbert (timeVector a) := by
  have h := past_gradient_expansion (fun _ : Fin 1 => a) polynomial
  have hc := pastCoefficient_coeFn (fun _ : Fin 1 => a) (pderiv 0 polynomial)
  filter_upwards [h, hc] with ω hd hc
  simp only [Fin.sum_univ_one] at hd
  simpa [polynomial] using hd.trans (congrArg
    (fun r : ℝ => r • hilbertEmbedding TimeHilbert (timeVector a)) hc)

theorem sensitivity_coeFn (a b : ℝ≥0) (hab : a ≤ b) :
    incrementSensitivity (fun _ : Fin 1 => a) polynomial a b =ᵐ[gaussianProduct]
      fun ω => (2 * process a ω * (process b ω - process a ω)) •
        hilbertEmbedding TimeHilbert (timeVector a) := by
  filter_upwards [incrementSensitivity_coeFn (fun _ : Fin 1 => a) polynomial a b hab,
    coefficient_derivative a] with ω hs hd
  rw [hs, hd, smul_smul]
  congr 1
  ring

theorem sensitivity_eq (a b : ℝ≥0) (hab : a ≤ b) :
    incrementSensitivity (fun _ : Fin 1 => a) polynomial a b =
      scalarTensor (hilbertEmbedding TimeHilbert (timeVector a))
        ((2 : ℝ) • incrementProductL2 (fun _ : Fin 1 => a) (X 0) a b) := by
  apply Lp.ext
  filter_upwards [sensitivity_coeFn a b hab,
    scalarTensor_coeFn (hilbertEmbedding TimeHilbert (timeVector a))
      ((2 : ℝ) • incrementProductL2 (fun _ : Fin 1 => a) (X 0) a b),
    Lp.coeFn_smul (2 : ℝ) (incrementProductL2 (fun _ : Fin 1 => a) (X 0) a b),
    incrementProductL2_coeFn (fun _ : Fin 1 => a) (X 0) a b] with ω hs ht hm hi
  rw [hs, ht, hm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hi]
  simp only [eval_X]
  congr 1
  ring

theorem linearCoefficient_norm_sq (a : ℝ≥0) :
    ‖(pastCoefficient (fun _ : Fin 1 => a) (X 0) : GaussianL2)‖ ^ 2 = (a : ℝ) := by
  have he : (pastCoefficient (fun _ : Fin 1 => a) (X 0) : GaussianL2) = wienerL2 a := by
    apply Lp.ext
    simpa [GaussianTimeProcess.process] using pastCoefficient_coeFn (fun _ : Fin 1 => a) (X 0)
  rw [he]
  change ‖GaussianHilbertProcess.isonormalEmbedding TimeHilbert (timeVector a)‖ ^ 2 = _
  rw [LinearIsometry.norm_map, timeVector_norm_sq]

theorem sensitivity_norm_sq (a b : ℝ≥0) (hab : a ≤ b) :
    ‖incrementSensitivity (fun _ : Fin 1 => a) polynomial a b‖ ^ 2 =
      4 * (a : ℝ)^2 * ((b : ℝ) - a) := by
  rw [sensitivity_eq a b hab, ← real_inner_self_eq_norm_sq, scalarTensor_pair_inner,
    real_inner_smul_left, real_inner_smul_right,
    incrementProduct_inner _ _ a b _ _ a b (fun _ => le_rfl) (fun _ => le_rfl) hab hab,
    scalarTensor_pair_inner]
  simp only [real_inner_self_eq_norm_sq, (hilbertEmbedding TimeHilbert).norm_map,
    timeVector_norm_sq, incrementDirection_norm_sq a b hab, linearCoefficient_norm_sq]
  ring

theorem sensitivity_ne_zero (a b : ℝ≥0) (ha : 0 < a) (hab : a < b) :
    incrementSensitivity (fun _ : Fin 1 => a) polynomial a b ≠ 0 := by
  intro hz
  have h := sensitivity_norm_sq a b hab.le
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  have ha' : (0 : ℝ) < a := ha
  have hab' : (a : ℝ) < b := hab
  have hp : 0 < 4 * (a : ℝ)^2 * ((b : ℝ) - a) := by positivity
  linarith

def initialField (a : ℝ≥0) : fullPredictable :=
  pastStep 0 a (fun _ : Fin 1 => 0) (fun _ => le_rfl) 1

def volatilityField (a b : ℝ≥0) : fullPredictable := initialField a + delayedField a b

theorem volatilityField_sobolev (a b : ℝ≥0) :
    (volatilityField a b : TimeProbabilityL2) ∈ predictableSobolev :=
  predictableSobolev.add_mem
    (past_polynomial_step_mem_predictableSobolev 0 a (fun _ : Fin 1 => 0)
      (fun _ => le_rfl) 1) (delayedField_sobolev a b)

theorem initialField_coe (a : ℝ≥0) :
    (initialField a : TimeProbabilityL2) = productTensor (timeVector a) gaussianOne := by
  have he : (pastCoefficient (fun _ : Fin 1 => (0 : ℝ≥0)) 1 : GaussianL2) = gaussianOne := by
    apply Lp.ext
    filter_upwards [pastCoefficient_coeFn (fun _ : Fin 1 => (0 : ℝ≥0)) 1,
      gaussianOne_coeFn] with ω hc ho
    simp only [map_one] at hc
    exact hc.trans ho.symm
  change productTensor (intervalVector 0 a) _ = _
  rw [he]
  rfl

theorem initial_integral (a : ℝ≥0) : itoIntegral (initialField a) = wienerL2 a := by
  rw [initialField, ito_pastStep 0 a (show 0 ≤ a from bot_le)]
  apply Lp.ext
  filter_upwards [incrementProductL2_coeFn (fun _ : Fin 1 => (0 : ℝ≥0)) 1 0 a,
    process_zero_ae] with ω hi hz
  simp only [map_one, one_mul, hz, sub_zero] at hi
  exact hi

theorem volatility_integral (a b : ℝ≥0) (hab : a ≤ b) :
    itoIntegral (volatilityField a b) =ᵐ[gaussianProduct]
      fun ω => process a ω + (1 + process a ω ^ 2) * (process b ω - process a ω) := by
  rw [volatilityField, map_add, initial_integral]
  filter_upwards [Lp.coeFn_add (wienerL2 a) (itoIntegral (delayedField a b)),
    delayed_integral_coeFn a b hab] with ω ha hd
  simpa only [Pi.add_apply, hd, GaussianTimeProcess.process] using ha

theorem delayed_derivative_graph (a b : ℝ≥0) (hab : a ≤ b) :
    (itoIntegral (delayedField a b), fieldEmbedding (delayedField a b) +
      incrementSensitivity (fun _ : Fin 1 => a) polynomial a b) ∈
        closedCylindricalDerivative.graph := by
  rw [delayedField, ito_pastStep a b hab]
  change (incrementProductL2 _ _ _ _, fieldEmbedding (productTensor _ _) + _) ∈ _
  rw [fieldEmbedding_tensor]
  exact incrementProduct_closedDerivative_graph _ _ _ _ hab

theorem volatility_derivative_graph (a b : ℝ≥0) (hab : a ≤ b) :
    (itoIntegral (volatilityField a b), fieldEmbedding (volatilityField a b) +
      incrementSensitivity (fun _ : Fin 1 => a) polynomial a b) ∈
        closedCylindricalDerivative.graph := by
  have hi : (itoIntegral (initialField a), fieldEmbedding (initialField a)) ∈
      closedCylindricalDerivative.graph := by
    rw [initial_integral, initialField_coe]
    exact GaussianDeterministicIntegral.firstChaos_closedDerivative_graph (timeVector a)
  have hh := closedCylindricalDerivative.graph.add_mem hi (delayed_derivative_graph a b hab)
  simpa [volatilityField, map_add, Prod.mk_add_mk, add_assoc] using hh

theorem volatility_not_original_derivative (a b : ℝ≥0) (ha : 0 < a) (hab : a < b) :
    (itoIntegral (volatilityField a b), fieldEmbedding (volatilityField a b)) ∉
      closedCylindricalDerivative.graph := by
  intro h
  have he := closedCylindricalDerivative.mem_graph_snd_inj
    (volatility_derivative_graph a b hab.le) h rfl
  exact sensitivity_ne_zero a b ha hab (add_left_cancel (he.trans (add_zero _).symm))

theorem volatilityField_coeFn (a b : ℝ≥0) :
    (volatilityField a b : TimeProbabilityL2) =ᵐ[timeProbability] fun z =>
      (Ioc 0 (a : ℝ)).indicator (fun _ => (1 : ℝ)) z.1 +
        (Ioc (a : ℝ) (b : ℝ)).indicator (fun _ => (1 : ℝ)) z.1 * (1 + process a z.2 ^ 2) := by
  have hi := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (timeVector_coeFn a)
  have hj := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (intervalVector_coeFn a b)
  have hc := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp (coefficient_coeFn a)
  have ho := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ))
    (ν := gaussianProduct)).ae_eq_comp gaussianOne_coeFn
  change ((initialField a : TimeProbabilityL2) + delayedField a b) =ᵐ[_] _
  rw [initialField_coe]
  filter_upwards [Lp.coeFn_add (productTensor (timeVector a) gaussianOne)
      (delayedField a b), productTensor_coeFn (timeVector a) gaussianOne,
    productTensor_coeFn (intervalVector a b)
      (pastCoefficient (fun _ : Fin 1 => a) polynomial), hi, hj, hc, ho]
    with z hs hb hd hi hj hc ho
  change (delayedField a b : TimeProbabilityL2) z = _ at hd
  simp only [Function.comp_apply] at hi hj hc ho
  simp only [hs, Pi.add_apply, hb, hd, hi, hj, hc, ho, mul_one]

theorem volatilityField_lower (a b : ℝ≥0) :
    ∀ᵐ z ∂timeProbability, z ∈ PredictableRealL2.horizon b →
      1 ≤ (volatilityField a b : TimeProbabilityL2) z := by
  filter_upwards [volatilityField_coeFn a b] with z hz hzb
  rw [hz]
  have hx : 0 < z.1 ∧ z.1 ≤ (b : ℝ) := hzb.1
  by_cases hza : z.1 ≤ (a : ℝ)
  · have hi : z.1 ∈ Ioc 0 (a : ℝ) := ⟨hx.1, hza⟩
    have hj : z.1 ∉ Ioc (a : ℝ) (b : ℝ) := fun h => (not_lt_of_ge hza) h.1
    simp [hi, hj]
  · have hi : z.1 ∉ Ioc 0 (a : ℝ) := fun h => hza h.2
    have hj : z.1 ∈ Ioc (a : ℝ) (b : ℝ) := ⟨lt_of_not_ge hza, hx.2⟩
    simp only [indicator_of_notMem hi, indicator_of_mem hj, zero_add, one_mul]
    linarith [sq_nonneg (process a z.2)]

/-- This is randomness in the actual time-probability L² class, not a choice of representative. -/
theorem volatilityField_not_deterministic (a b : ℝ≥0) (ha : 0 < a) (hab : a < b) :
    ¬ ∃ q : TimeHilbert, (volatilityField a b : TimeProbabilityL2) =
      productTensor q gaussianOne := by
  rintro ⟨q, hq⟩
  have hqp : productTensor q gaussianOne ∈ fullPredictable := hq ▸ (volatilityField a b).property
  have he : (⟨productTensor q gaussianOne, hqp⟩ : fullPredictable) = volatilityField a b :=
    Subtype.ext hq.symm
  have hg := GaussianDeterministicGraphCore.deterministic_integral_derivative q hqp
  rw [he, ← hq] at hg
  exact volatility_not_original_derivative a b ha hab hg
end OperatorDerivativeRewrite.Foundation.GaussianPositiveVolatility
