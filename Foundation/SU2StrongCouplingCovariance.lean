import Foundation.SU2LagEventCorrelation
import Foundation.SU2CoupledLoopResponse
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.Measure

/-! Exact stationary covariance and its strong-coupling saturation for the SU(2) loop chain. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Real
open scoped Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.SU2LoopEquilibrium
open OperatorDerivativeRewrite.Foundation.SU2CoupledLoopResponse
open OperatorDerivativeRewrite.Foundation.SU2LagEventCorrelation

namespace OperatorDerivativeRewrite.Foundation.SU2StrongCouplingCovariance

theorem lagKernel_one (r : ℝ) : lagKernel r 1 = loopKernel r := by
  simp [lagKernel]

theorem stationaryLagLaw_one (r : ℝ) : stationaryLagLaw r 1 = coupledLaw r := by
  rw [stationaryLagLaw, lagKernel_one]
  exact equilibrium_edge r

def lagCov (r : ℝ) (n : ℕ) : ℝ :=
  (∫ p, X p ∂stationaryLagLaw r n) -
    (∫ p, F p ∂stationaryLagLaw r n) *
      (∫ p, G p ∂stationaryLagLaw r n)

theorem lagCov_one (r : ℝ) : lagCov r 1 = corr r := by
  rw [lagCov, stationaryLagLaw_one, corr_eq_covariance]

theorem lagCov_hasDerivAt_zero : HasDerivAt (fun r => lagCov r 1) (1/16) 0 := by
  simpa only [lagCov_one] using corr_hasDerivAt_zero

theorem positive_lagCov_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ 0 < lagCov r 1 := by
  obtain ⟨r, hr, hrε, hc⟩ := positive_corr_near_zero ε hε
  exact ⟨r, hr, hrε, by simpa [lagCov_one] using hc⟩

private theorem halfTrace_continuous : Continuous halfTrace := by
  have he : halfTrace = fun A : SU2 => ((A : SU2TraceHessianModel.M2) 0 0).re / 2 +
      ((A : SU2TraceHessianModel.M2) 1 1).re / 2 := by
    funext A
    simp [halfTrace, SU2TraceHessianModel.traceReal, Matrix.trace_fin_two, add_div]
  rw [he]
  have hentry (i j : Fin 2) : Continuous (fun A : SU2 => (A : SU2TraceHessianModel.M2) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact (((Complex.continuous_re.comp (hentry 0 0)).div_const 2).add
    ((Complex.continuous_re.comp (hentry 1 1)).div_const 2))

private theorem X_continuous : Continuous X :=
  (halfTrace_continuous.comp continuous_fst).mul
    (halfTrace_continuous.comp continuous_snd)

private def upperCap (δ : ℝ) : Set (SU2 × SU2) := {p | 1-δ/2 < X p}

private theorem upperCap_mass_pos (δ : ℝ) (hδ : 0 < δ) :
    0 < μ.real (upperCap δ) := by
  haveI : μ.IsOpenPosMeasure := by
    unfold μ
    infer_instance
  have ht : IsOpen (upperCap δ) := isOpen_lt continuous_const X_continuous
  have hm : ((1 : SU2), (1 : SU2)) ∈ upperCap δ := by
    simp [upperCap, X, F, G, SU2OpenLinkGaugeObstruction.halfTrace_one]
    linarith
  have hp : 0 < μ (upperCap δ) := IsOpen.measure_pos μ ht ⟨(1, 1), hm⟩
  rw [Measure.real]
  exact ENNReal.toReal_pos hp.ne' (measure_lt_top _ _).ne

private theorem X_measurable : Measurable X :=
  (halfTrace_measurable.comp measurable_fst).mul
    (halfTrace_measurable.comp measurable_snd)

private theorem X_bound (p : SU2 × SU2) : |X p| ≤ 1 := by
  rw [X, abs_mul]
  calc
    |halfTrace p.1| * |halfTrace p.2| ≤ 1 * 1 :=
      mul_le_mul (halfTrace_bound _) (halfTrace_bound _) (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

private theorem partition_lower (δ r : ℝ) (hr : 0 ≤ r) :
    μ.real (upperCap δ) * Real.exp (r * (1-δ/2)) ≤
      BoundedExponentialTiltResponse.partition μ X r := by
  have hs : MeasurableSet (upperCap δ) :=
    measurableSet_lt measurable_const X_measurable
  have hi := BoundedExponentialTiltResponse.exponential_integrable μ X
    X_measurable X_bound r
  have hc : Integrable (fun _ : SU2 × SU2 => Real.exp (r*(1-δ/2))) μ :=
    integrable_const _
  have h1 :
      (∫ p in upperCap δ, Real.exp (r*(1-δ/2)) ∂μ) ≤
      (∫ p in upperCap δ, Real.exp (r*X p) ∂μ) := by
    apply setIntegral_mono_on hc.integrableOn hi.integrableOn hs
    intro p hp
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hp) hr)
  have h2 :
      (∫ p in upperCap δ, Real.exp (r*X p) ∂μ) ≤
      (∫ p, Real.exp (r*X p) ∂μ) := by
    apply setIntegral_le_integral hi
    exact Eventually.of_forall (fun p => (Real.exp_pos _).le)
  have he : (∫ p in upperCap δ, Real.exp (r*(1-δ/2)) ∂μ) =
      μ.real (upperCap δ) * Real.exp (r*(1-δ/2)) := by
    simp [setIntegral_const, smul_eq_mul]
  rw [← he]
  simpa only [BoundedExponentialTiltResponse.partition,
    BoundedExponentialTiltResponse.weighted, one_mul] using h1.trans h2

private def lowerCap (δ : ℝ) : Set (SU2 × SU2) := {p | X p ≤ 1-δ}

private theorem lower_integral_upper (δ r : ℝ) (hr : 0 ≤ r) :
    (∫ p in lowerCap δ, Real.exp (r * X p) ∂μ) ≤
      Real.exp (r * (1-δ)) := by
  have hs : MeasurableSet (lowerCap δ) :=
    measurableSet_le X_measurable measurable_const
  have hi := BoundedExponentialTiltResponse.exponential_integrable μ X
    X_measurable X_bound r
  have hc : Integrable (fun _ : SU2 × SU2 => Real.exp (r*(1-δ))) μ :=
    integrable_const _
  have h1 :
      (∫ p in lowerCap δ, Real.exp (r*X p) ∂μ) ≤
      (∫ p in lowerCap δ, Real.exp (r*(1-δ)) ∂μ) := by
    apply setIntegral_mono_on hi.integrableOn hc.integrableOn hs
    intro p hp
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp hr)
  have h2 :
      (∫ p in lowerCap δ, Real.exp (r*(1-δ)) ∂μ) ≤
      (∫ p, Real.exp (r*(1-δ)) ∂μ) := by
    apply setIntegral_le_integral hc
    exact Eventually.of_forall (fun p => (Real.exp_pos _).le)
  simpa using h1.trans h2

private theorem tilted_lowerCap_mass (δ r : ℝ) :
    (coupledLaw r).real (lowerCap δ) =
      (∫ p in lowerCap δ, Real.exp (r*X p) ∂μ) /
        BoundedExponentialTiltResponse.partition μ X r := by
  have hs : MeasurableSet (lowerCap δ) :=
    measurableSet_le X_measurable measurable_const
  let f : SU2 × SU2 → ℝ := (lowerCap δ).indicator (fun _ => 1)
  have ht := BoundedExponentialTiltResponse.tilted_integral μ X f
    X_measurable X_bound r
  have hl : (∫ p, f p ∂coupledLaw r) =
      (coupledLaw r).real (lowerCap δ) := by
    exact integral_indicator_one hs
  have hr : (∫ p, f p * Real.exp (r*X p) ∂μ) =
      (∫ p in lowerCap δ, Real.exp (r*X p) ∂μ) := by
    have he : (fun p => f p * Real.exp (r*X p)) =
        (lowerCap δ).indicator (fun p => Real.exp (r*X p)) := by
      funext p
      by_cases hp : p ∈ lowerCap δ <;> simp [f, hp]
    rw [he, integral_indicator hs]
  change (∫ p, f p ∂coupledLaw r) = _ at ht
  rw [hl] at ht
  change _ = (∫ p, f p * Real.exp (r*X p) ∂μ) /
    BoundedExponentialTiltResponse.partition μ X r at ht
  rw [hr] at ht
  exact ht

private theorem tilted_lowerCap_bound (δ r : ℝ) (hδ : 0 < δ) (hr : 0 ≤ r) :
    (coupledLaw r).real (lowerCap δ) ≤
      Real.exp (-(r*δ/2)) / μ.real (upperCap δ) := by
  let c := μ.real (upperCap δ)
  let z := BoundedExponentialTiltResponse.partition μ X r
  let n := ∫ p in lowerCap δ, Real.exp (r*X p) ∂μ
  have hc : 0 < c := upperCap_mass_pos δ hδ
  have hz : 0 < z := BoundedExponentialTiltResponse.partition_pos μ X
    X_measurable X_bound r
  have hden : c * Real.exp (r*(1-δ/2)) ≤ z := partition_lower δ r hr
  have hnum : n ≤ Real.exp (r*(1-δ)) := lower_integral_upper δ r hr
  rw [tilted_lowerCap_mass]
  change n / z ≤ Real.exp (-(r*δ/2)) / c
  apply (div_le_div_iff₀ hz hc).mpr
  calc
    n * c ≤ Real.exp (r*(1-δ)) * c := mul_le_mul_of_nonneg_right hnum hc.le
    _ = Real.exp (-(r*δ/2)) * (c * Real.exp (r*(1-δ/2))) := by
      calc
        Real.exp (r*(1-δ)) * c = c * Real.exp (r*(1-δ)) := mul_comm _ _
        _ = c * Real.exp (-(r*δ/2) + r*(1-δ/2)) := by congr 1; ring
        _ = Real.exp (-(r*δ/2)) * (c * Real.exp (r*(1-δ/2))) := by
          rw [Real.exp_add]
          ring
    _ ≤ Real.exp (-(r*δ/2)) * z :=
      mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le

private theorem tail_tendsto_zero (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun r : ℝ => (coupledLaw r).real (lowerCap δ)) atTop (𝓝 0) := by
  let c := μ.real (upperCap δ)
  have hc : 0 < c := upperCap_mass_pos δ hδ
  have hneg : -(δ/2) < 0 := by linarith
  have ht : Tendsto (fun r : ℝ => Real.exp ((-(δ/2))*r)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
  have hupper : Tendsto (fun r : ℝ => Real.exp (-(r*δ/2))/c) atTop (𝓝 0) := by
    convert ht.div_const c using 1 <;> simp [show (0:ℝ)/c=0 by simp]
    funext r
    congr 1
    ring
  apply squeeze_zero' (Eventually.of_forall (fun r => measureReal_nonneg)) ?_ hupper
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
  exact tilted_lowerCap_bound δ r hδ hr

private theorem mean_defect_bound (δ r : ℝ) (hδ : 0 ≤ δ) :
    1 - (∫ p, X p ∂coupledLaw r) ≤
      δ + 2 * (coupledLaw r).real (lowerCap δ) := by
  let ν := coupledLaw r
  let f : SU2 × SU2 → ℝ := (lowerCap δ).indicator (fun _ => 1)
  letI : IsProbabilityMeasure ν := coupledLaw_probability r
  have hs : MeasurableSet (lowerCap δ) :=
    measurableSet_le X_measurable measurable_const
  have hiX : Integrable X ν := by
    apply Integrable.mono' (integrable_const (1:ℝ)) X_measurable.aestronglyMeasurable
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using X_bound p
  have hif : Integrable f ν := by
    apply Integrable.mono' (integrable_const (1:ℝ))
      (measurable_const.indicator hs).aestronglyMeasurable
    filter_upwards with p
    by_cases hp : p ∈ lowerCap δ <;> simp [f, hp]
  have hpoint (p : SU2 × SU2) : 1-X p ≤ δ + 2*f p := by
    by_cases hp : p ∈ lowerCap δ
    · have hx := X_bound p
      simp [f, hp]
      linarith [abs_le.mp hx]
    · have hx : 1-δ < X p := lt_of_not_ge (by simpa [lowerCap] using hp)
      simp [f, hp]
      linarith
  have hm := integral_mono (μ := ν) ((integrable_const (1:ℝ)).sub hiX)
    ((integrable_const δ).add (hif.const_mul 2)) hpoint
  have hfint : (∫ p, f p ∂ν) = ν.real (lowerCap δ) := integral_indicator_one hs
  change (∫ p, (1-X p) ∂ν) ≤ (∫ p, (δ+2*f p) ∂ν) at hm
  rw [integral_sub (integrable_const (1:ℝ)) hiX,
    integral_add (integrable_const δ) (hif.const_mul 2),
    integral_const_mul] at hm
  simpa [hfint] using hm

private theorem mean_le_one (r : ℝ) : (∫ p, X p ∂coupledLaw r) ≤ 1 := by
  let ν := coupledLaw r
  letI : IsProbabilityMeasure ν := coupledLaw_probability r
  have hiX : Integrable X ν := by
    apply Integrable.mono' (integrable_const (1:ℝ)) X_measurable.aestronglyMeasurable
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using X_bound p
  have hm := integral_mono hiX (integrable_const (1:ℝ))
    (fun p => (abs_le.mp (X_bound p)).2)
  simpa [ν] using hm

theorem interaction_mean_tendsto_one :
    Tendsto (fun r : ℝ => ∫ p, X p ∂coupledLaw r) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let δ : ℝ := (1-a)/2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hsmall : 0 < (1-a)/4 := by linarith
    have ht := (tendsto_order.mp (tail_tendsto_zero δ hδ)).2 ((1-a)/4) hsmall
    filter_upwards [ht] with r htail
    have hb := mean_defect_bound δ r hδ.le
    change (coupledLaw r).real (lowerCap δ) < (1-a)/4 at htail
    dsimp [δ] at hb
    linarith
  · intro b hb
    exact Eventually.of_forall (fun r => lt_of_le_of_lt (mean_le_one r) hb)

private theorem halfTrace_minus (B : SU2) :
    halfTrace (SU2StapleExtremes.minusOne * B) = -halfTrace B := by
  simp [halfTrace, SU2StapleExtremes.minusOne,
    QuaternionSU2Representation.hom, QuaternionSU2Representation.repr,
    SU2TraceHessianModel.traceReal, Matrix.trace_fin_two, Matrix.mul_apply,
    Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two]
  ring

private def centerFlip : SU2 × SU2 :=
  (SU2StapleExtremes.minusOne, SU2StapleExtremes.minusOne)

private instance : MeasurableMul (SU2 × SU2) where
  measurable_const_mul c :=
    ((measurable_const_mul c.1).comp measurable_fst).prodMk
      ((measurable_const_mul c.2).comp measurable_snd)
  measurable_mul_const c :=
    ((measurable_mul_const c.1).comp measurable_fst).prodMk
      ((measurable_mul_const c.2).comp measurable_snd)

private instance : μ.IsMulLeftInvariant := by
  unfold μ
  infer_instance

private theorem X_centerFlip (p : SU2 × SU2) : X (centerFlip * p) = X p := by
  simp [X, F, G, centerFlip, halfTrace_minus]

private theorem F_centerFlip (p : SU2 × SU2) : F (centerFlip * p) = -F p := by
  simp [F, centerFlip, halfTrace_minus]

private theorem G_centerFlip (p : SU2 × SU2) : G (centerFlip * p) = -G p := by
  simp [G, centerFlip, halfTrace_minus]

private theorem weighted_F_zero (r : ℝ) :
    BoundedExponentialTiltResponse.weighted μ X F r = 0 := by
  have he := integral_mul_left_eq_self (μ := μ)
    (fun p : SU2 × SU2 => F p * Real.exp (r*X p)) centerFlip
  have hf : (fun p : SU2 × SU2 => F (centerFlip*p) * Real.exp (r*X (centerFlip*p))) =
      (fun p => -(F p * Real.exp (r*X p))) := by
    funext p
    rw [F_centerFlip, X_centerFlip]
    ring
  rw [hf, integral_neg] at he
  have hz : (∫ p, F p * Real.exp (r*X p) ∂μ) = 0 := by linarith
  simpa [BoundedExponentialTiltResponse.weighted] using hz

private theorem weighted_G_zero (r : ℝ) :
    BoundedExponentialTiltResponse.weighted μ X G r = 0 := by
  have he := integral_mul_left_eq_self (μ := μ)
    (fun p : SU2 × SU2 => G p * Real.exp (r*X p)) centerFlip
  have hf : (fun p : SU2 × SU2 => G (centerFlip*p) * Real.exp (r*X (centerFlip*p))) =
      (fun p => -(G p * Real.exp (r*X p))) := by
    funext p
    rw [G_centerFlip, X_centerFlip]
    ring
  rw [hf, integral_neg] at he
  have hz : (∫ p, G p * Real.exp (r*X p) ∂μ) = 0 := by linarith
  simpa [BoundedExponentialTiltResponse.weighted] using hz

theorem stationary_F_mean_zero (r : ℝ) :
    (∫ p, F p ∂coupledLaw r) = 0 := by
  rw [coupledLaw, BoundedExponentialTiltResponse.tilted_integral μ X F
    X_measurable X_bound]
  simp [BoundedExponentialTiltResponse.expectation, weighted_F_zero]

theorem stationary_G_mean_zero (r : ℝ) :
    (∫ p, G p ∂coupledLaw r) = 0 := by
  rw [coupledLaw, BoundedExponentialTiltResponse.tilted_integral μ X G
    X_measurable X_bound]
  simp [BoundedExponentialTiltResponse.expectation, weighted_G_zero]

theorem corr_eq_interaction_mean (r : ℝ) :
    corr r = ∫ p, X p ∂coupledLaw r := by
  rw [corr_eq_covariance, stationary_F_mean_zero, stationary_G_mean_zero]
  ring

theorem stationary_lag_one_cov_tendsto_one :
    Tendsto (fun r : ℝ => lagCov r 1) atTop (𝓝 1) := by
  have he : (fun r : ℝ => lagCov r 1) =
      (fun r : ℝ => ∫ p, X p ∂coupledLaw r) := by
    funext r
    rw [lagCov_one, corr_eq_interaction_mean]
  rw [he]
  exact interaction_mean_tendsto_one

theorem no_uniform_stationary_lag_one_cov_bound (q : ℝ) (hq : q < 1) :
    ∃ r : ℝ, 0 ≤ r ∧ q < lagCov r 1 := by
  have hqev := (tendsto_order.mp stationary_lag_one_cov_tendsto_one).1 q hq
  exact (hqev.and (eventually_ge_atTop (0 : ℝ))).exists.elim
    (fun r hr => ⟨r, hr.2, hr.1⟩)

theorem nonpositive_interaction_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 ≤ r →
      (coupledLaw r).real {p | X p ≤ 0} ≤ c * Real.exp (-r/2) := by
  refine ⟨(μ.real (upperCap 1))⁻¹, inv_pos.mpr (upperCap_mass_pos 1 (by norm_num)), ?_⟩
  intro r hr
  simpa [lowerCap, div_eq_mul_inv, mul_comm, neg_div] using
    tilted_lowerCap_bound 1 r (by norm_num) hr

theorem center_odd_mean_zero (r : ℝ) (f : SU2 × SU2 → ℝ)
    (hf : Measurable f) (hb : ∀ p, |f p| ≤ 1)
    (hodd : ∀ p, f (SU2StapleExtremes.minusOne*p.1,
      SU2StapleExtremes.minusOne*p.2) = -f p) :
    (∫ p, f p ∂coupledLaw r) = 0 := by
  have he := integral_mul_left_eq_self (μ := μ)
    (fun p : SU2 × SU2 => f p * Real.exp (r*X p)) centerFlip
  have heq : (fun p : SU2 × SU2 => f (centerFlip*p) * Real.exp (r*X (centerFlip*p))) =
      (fun p => -(f p * Real.exp (r*X p))) := by
    funext p
    rw [X_centerFlip]
    change f (SU2StapleExtremes.minusOne*p.1, SU2StapleExtremes.minusOne*p.2) * _ = _
    rw [hodd]
    ring
  rw [heq, integral_neg] at he
  have hz : BoundedExponentialTiltResponse.weighted μ X f r = 0 := by
    unfold BoundedExponentialTiltResponse.weighted
    linarith
  rw [coupledLaw, BoundedExponentialTiltResponse.tilted_integral μ X f X_measurable X_bound]
  simp [BoundedExponentialTiltResponse.expectation, hz]

theorem halfTrace_center_neg (C : SU2) :
    halfTrace (SU2StapleExtremes.minusOne*C) = -halfTrace C := halfTrace_minus C

end OperatorDerivativeRewrite.Foundation.SU2StrongCouplingCovariance
