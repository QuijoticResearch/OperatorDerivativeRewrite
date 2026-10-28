import Foundation.SU2TwoLoopJointLaw
/-! Gauge-invariant two-loop Gibbs coupling and its exact first-order connected-correlation response. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.BoundedExponentialTiltResponse
namespace OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse

def μ : Measure (SU2 × SU2) := law.prod law
def F (p : SU2 × SU2) : ℝ := halfTrace p.1
def G (p : SU2 × SU2) : ℝ := halfTrace p.2
def X (p : SU2 × SU2) : ℝ := F p * G p

def corr (r : ℝ) : ℝ :=
  expectation μ X X r - expectation μ X F r * expectation μ X G r

private theorem hF : Measurable F := halfTrace_measurable.comp measurable_fst
private theorem hG : Measurable G := halfTrace_measurable.comp measurable_snd
private theorem hX : Measurable X := hF.mul hG
private theorem bF (p : SU2 × SU2) : |F p| ≤ 1 := halfTrace_bound p.1
private theorem bG (p : SU2 × SU2) : |G p| ≤ 1 := halfTrace_bound p.2
private theorem bX (p : SU2 × SU2) : |X p| ≤ 1 := by
  rw [X, abs_mul]
  calc
    |F p| * |G p| ≤ 1 * 1 := mul_le_mul (bF p) (bG p) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

private theorem meanF : (∫ p, F p ∂μ) = 0 := by
  have h := integral_prod_mul (μ := law) (ν := law) halfTrace (fun _ : SU2 => (1 : ℝ))
  change (∫ p, halfTrace p.1 ∂law.prod law) = 0
  simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1] using h

private theorem meanG : (∫ p, G p ∂μ) = 0 := by
  have h := integral_prod_mul (μ := law) (ν := law) (fun _ : SU2 => (1 : ℝ)) halfTrace
  change (∫ p, halfTrace p.2 ∂law.prod law) = 0
  simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1] using h

private theorem meanX : (∫ p, X p ∂μ) = 0 := by
  have h := integral_prod_mul (μ := law) (ν := law) halfTrace halfTrace
  change (∫ p, halfTrace p.1 * halfTrace p.2 ∂law.prod law) = 0
  simpa [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1] using h

private theorem meanXX : (∫ p, X p * X p ∂μ) = 1/16 := by
  have h := integral_prod_mul (μ := law) (ν := law)
    (fun A : SU2 => halfTrace A^2) (fun B : SU2 => halfTrace B^2)
  have hh : (∫ p, X p * X p ∂μ) =
      (∫ p, halfTrace p.1^2 * halfTrace p.2^2 ∂μ) := by
    apply integral_congr_ae; filter_upwards with p; simp [X,F,G]; ring
  rw [hh]
  change (∫ p, halfTrace p.1^2 * halfTrace p.2^2 ∂law.prod law) = 1/16
  rw [h]
  rw [(OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).2.1]
  norm_num

private theorem meanFX : (∫ p, F p * X p ∂μ) = 0 := by
  have h := integral_prod_mul (μ := law) (ν := law)
    (fun A : SU2 => halfTrace A^2) halfTrace
  have hh : (∫ p, F p * X p ∂μ) =
      (∫ p, halfTrace p.1^2 * halfTrace p.2 ∂μ) := by
    apply integral_congr_ae; filter_upwards with p; simp [X,F,G]; ring
  rw [hh]
  change (∫ p, halfTrace p.1^2 * halfTrace p.2 ∂law.prod law) = 0
  rw [h, (OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1]
  simp

private theorem meanGX : (∫ p, G p * X p ∂μ) = 0 := by
  have h := integral_prod_mul (μ := law) (ν := law)
    halfTrace (fun B : SU2 => halfTrace B^2)
  have hh : (∫ p, G p * X p ∂μ) =
      (∫ p, halfTrace p.1 * halfTrace p.2^2 ∂μ) := by
    apply integral_congr_ae; filter_upwards with p; simp [X,F,G]; ring
  rw [hh]
  change (∫ p, halfTrace p.1 * halfTrace p.2^2 ∂law.prod law) = 0
  rw [h, (OperatorDerivativeRewrite.Foundation.SU2TiltEnergyResponse.moment_values law).1]
  simp


instance μ_probability : IsProbabilityMeasure μ := by
  unfold μ
  infer_instance

def coupledLaw (r : ℝ) : Measure (SU2 × SU2) := tiltedMeasure μ X r

theorem coupledLaw_zero : coupledLaw 0 = μ := by
  simp [coupledLaw, tiltedMeasure, density, partition_zero]

theorem coupledLaw_zero_actual_chain (A : SU2) :
    coupledLaw 0 =
      (SU2OneWordTransfer.transition law 0 A ⊗ₘ SU2OneWordTransfer.transition law 0).map
        (fun p : SU2 × SU2 => (A * p.1, p.1 * p.2)) := by
  rw [coupledLaw_zero]
  simpa [μ, OperatorDerivativeRewrite.Foundation.SU2StapleExtremes.zero_tilt] using
    (OperatorDerivativeRewrite.Foundation.SU2TwoLoopJointLaw.two_loop_joint_law A 0).symm

theorem coupledLaw_probability (r : ℝ) : IsProbabilityMeasure (coupledLaw r) := by
  unfold coupledLaw
  exact tiltedMeasure_probability μ X hX bX r

theorem X_biGauge (g h : SU2) (p : SU2 × SU2) :
    X (g * p.1 * g⁻¹, h * p.2 * h⁻¹) = X p := by
  simp [X,F,G,halfTrace_conjugate]

def gaugeAction (g h : SU2) (p : SU2 × SU2) : SU2 × SU2 :=
  (g * p.1 * g⁻¹, h * p.2 * h⁻¹)

private theorem measurable_gaugeAction (g h : SU2) : Measurable (gaugeAction g h) := by
  exact ((measurable_mul_const g⁻¹).comp (measurable_const_mul g)).comp measurable_fst |>.prodMk
    (((measurable_mul_const h⁻¹).comp (measurable_const_mul h)).comp measurable_snd)

theorem μ_gauge_invariant (g h : SU2) : μ.map (gaugeAction g h) = μ := by
  unfold μ gaugeAction
  have hg : Measurable (fun C : SU2 => g * C * g⁻¹) :=
    (measurable_mul_const g⁻¹).comp (measurable_const_mul g)
  have hh : Measurable (fun C : SU2 => h * C * h⁻¹) :=
    (measurable_mul_const h⁻¹).comp (measurable_const_mul h)
  change (law.prod law).map
    (Prod.map (fun C : SU2 => g * C * g⁻¹) (fun C : SU2 => h * C * h⁻¹)) = law.prod law
  rw [← Measure.map_prod_map law law hg hh]
  rw [OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer.haar_conjugation_map,
    OperatorDerivativeRewrite.Foundation.SU2GaugeCovariantTransfer.haar_conjugation_map]

theorem coupledLaw_gauge_invariant (g h : SU2) (r : ℝ) :
    (coupledLaw r).map (gaugeAction g h) = coupledLaw r := by
  have hc := measurable_gaugeAction g h
  have hd : Measurable (fun p : SU2 × SU2 => ENNReal.ofReal (density μ X r p)) :=
    ((measurable_const.mul hX).exp.div_const _).ennreal_ofReal
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hc hs, coupledLaw, tiltedMeasure, withDensity_apply _ (hc hs),
    withDensity_apply _ hs]
  have he := setLIntegral_map (μ := μ) hs hd hc
  rw [μ_gauge_invariant] at he
  have hh : (fun p : SU2 × SU2 => ENNReal.ofReal (density μ X r p)) =
      (fun p => ENNReal.ofReal (density μ X r (gaugeAction g h p))) := by
    funext p
    simp [density, gaugeAction, X_biGauge]
  conv_lhs => rw [hh]
  exact he.symm

theorem corr_eq_covariance (r : ℝ) :
    corr r = (∫ p, X p ∂coupledLaw r) -
      (∫ p, F p ∂coupledLaw r) * (∫ p, G p ∂coupledLaw r) := by
  unfold corr coupledLaw
  rw [tilted_integral μ X X hX bX r,
    tilted_integral μ X F hX bX r,
    tilted_integral μ X G hX bX r]

theorem corr_hasDerivAt_zero : HasDerivAt corr (1/16) 0 := by
  have hdX := expectation_hasDerivAt_zero μ X X hX hX bX 1 (by norm_num) bX
  have hdF := expectation_hasDerivAt_zero μ X F hX hF bX 1 (by norm_num) bF
  have hdG := expectation_hasDerivAt_zero μ X G hX hG bX 1 (by norm_num) bG
  rw [meanXX, meanX] at hdX
  rw [meanFX, meanF, meanX] at hdF
  rw [meanGX, meanG, meanX] at hdG
  norm_num at hdX hdF hdG
  convert hdX.sub (hdF.mul hdG) using 1
  · funext r; rfl
  · simp

theorem positive_corr_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ 0 < corr r := by
  have h0 : corr 0 = 0 := by
    simp [corr, expectation_zero, meanX, meanF, meanG]
  obtain ⟨r, hr, hrε, hinc⟩ :=
    positive_derivative_arbitrarily_small_increase corr (1/16)
      corr_hasDerivAt_zero (by norm_num) ε hε
  rw [h0] at hinc
  exact ⟨r, hr, hrε, hinc⟩

end OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
