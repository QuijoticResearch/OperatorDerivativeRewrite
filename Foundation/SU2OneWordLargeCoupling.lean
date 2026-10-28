import Foundation.SU2OneWordBoundaryInfluence

/-! The actual one-word Haar transfer retains arbitrarily strong central-input influence at large coupling. This finite-dimensional obstruction does not address a gauge-compatible block transfer or continuum Yang--Mills. -/
noncomputable section
open MeasureTheory Filter Real
open scoped Topology
open OperatorDerivativeRewrite.Foundation
open QuaternionSU2Representation
namespace OperatorDerivativeRewrite.Foundation.SU2OneWordLargeCoupling

private def upperCap (δ : ℝ) : Set SU2 := {A | 1-δ/2 < halfTrace A}

private theorem partition_lower (δ β : ℝ) (hβ : 0 ≤ β) :
    law.real (upperCap δ) * Real.exp (β * (1-δ/2)) ≤
      BoundedExponentialTiltResponse.partition law halfTrace β := by
  have hs : MeasurableSet (upperCap δ) :=
    measurableSet_lt measurable_const halfTrace_measurable
  have hi := BoundedExponentialTiltResponse.exponential_integrable law halfTrace
    halfTrace_measurable halfTrace_bound β
  have hc : Integrable (fun _ : SU2 => Real.exp (β*(1-δ/2))) law := integrable_const _
  have h1 :
      (∫ A in upperCap δ, Real.exp (β*(1-δ/2)) ∂law) ≤
      (∫ A in upperCap δ, Real.exp (β*halfTrace A) ∂law) := by
    apply setIntegral_mono_on hc.integrableOn hi.integrableOn hs
    intro A hA
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_of_lt hA) hβ)
  have h2 :
      (∫ A in upperCap δ, Real.exp (β*halfTrace A) ∂law) ≤
      (∫ A, Real.exp (β*halfTrace A) ∂law) := by
    apply setIntegral_le_integral hi
    exact Eventually.of_forall (fun A => (Real.exp_pos _).le)
  have he : (∫ A in upperCap δ, Real.exp (β*(1-δ/2)) ∂law) =
      law.real (upperCap δ) * Real.exp (β*(1-δ/2)) := by
    simp [setIntegral_const, smul_eq_mul]
  rw [← he]
  simpa only [BoundedExponentialTiltResponse.partition, BoundedExponentialTiltResponse.weighted, one_mul] using h1.trans h2


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

private theorem halfTrace_one : halfTrace (1 : SU2) = 1 := by
  norm_num [halfTrace, SU2TraceHessianModel.traceReal, Matrix.trace_fin_two,
    Matrix.one_apply]

private theorem upperCap_mass_pos (δ : ℝ) (hδ : 0 < δ) : 0 < law.real (upperCap δ) := by
  have ht : IsOpen (upperCap δ) := isOpen_lt continuous_const halfTrace_continuous
  have hm : (1 : SU2) ∈ upperCap δ := by
    simp [upperCap, halfTrace_one]
    linarith
  have hp : 0 < law (upperCap δ) := IsOpen.measure_pos law ht ⟨1, hm⟩
  rw [Measure.real]
  exact ENNReal.toReal_pos hp.ne' (measure_lt_top _ _).ne

private def lowerCap (δ : ℝ) : Set SU2 := {A | halfTrace A ≤ 1-δ}

private theorem lower_integral_upper (δ β : ℝ) (hβ : 0 ≤ β) :
    (∫ A in lowerCap δ, Real.exp (β * halfTrace A) ∂law) ≤
      Real.exp (β * (1-δ)) := by
  have hs : MeasurableSet (lowerCap δ) :=
    measurableSet_le halfTrace_measurable measurable_const
  have hi := BoundedExponentialTiltResponse.exponential_integrable law halfTrace
    halfTrace_measurable halfTrace_bound β
  have hc : Integrable (fun _ : SU2 => Real.exp (β*(1-δ))) law := integrable_const _
  have h1 :
      (∫ A in lowerCap δ, Real.exp (β*halfTrace A) ∂law) ≤
      (∫ A in lowerCap δ, Real.exp (β*(1-δ)) ∂law) := by
    apply setIntegral_mono_on hi.integrableOn hc.integrableOn hs
    intro A hA
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hA hβ)
  have h2 :
      (∫ A in lowerCap δ, Real.exp (β*(1-δ)) ∂law) ≤
      (∫ A, Real.exp (β*(1-δ)) ∂law) := by
    apply setIntegral_le_integral hc
    exact Eventually.of_forall (fun A => (Real.exp_pos _).le)
  simpa using h1.trans h2

private theorem tilted_lowerCap_mass (δ β : ℝ) :
    (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).real (lowerCap δ) =
      (∫ A in lowerCap δ, Real.exp (β*halfTrace A) ∂law) /
        BoundedExponentialTiltResponse.partition law halfTrace β := by
  have hs : MeasurableSet (lowerCap δ) :=
    measurableSet_le halfTrace_measurable measurable_const
  let f : SU2 → ℝ := (lowerCap δ).indicator (fun _ => 1)
  have ht := BoundedExponentialTiltResponse.tilted_integral law halfTrace f
    halfTrace_measurable halfTrace_bound β
  have hl : (∫ A, f A ∂BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) =
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).real (lowerCap δ) := by
    exact integral_indicator_one hs
  have hr : (∫ A, f A * Real.exp (β*halfTrace A) ∂law) =
      (∫ A in lowerCap δ, Real.exp (β*halfTrace A) ∂law) := by
    have he : (fun A => f A * Real.exp (β*halfTrace A)) =
        (lowerCap δ).indicator (fun A => Real.exp (β*halfTrace A)) := by
      funext A
      by_cases hA : A ∈ lowerCap δ <;> simp [f, hA]
    rw [he, integral_indicator hs]
  rw [hl] at ht
  change _ = (∫ A, f A * Real.exp (β*halfTrace A) ∂law) /
    BoundedExponentialTiltResponse.partition law halfTrace β at ht
  rw [hr] at ht
  exact ht


private theorem tilted_lowerCap_bound (δ β : ℝ) (hδ : 0 < δ) (hβ : 0 ≤ β) :
    (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).real (lowerCap δ) ≤
      Real.exp (-(β*δ/2)) / law.real (upperCap δ) := by
  let c := law.real (upperCap δ)
  let z := BoundedExponentialTiltResponse.partition law halfTrace β
  let n := ∫ A in lowerCap δ, Real.exp (β*halfTrace A) ∂law
  have hc : 0 < c := upperCap_mass_pos δ hδ
  have hz : 0 < z := BoundedExponentialTiltResponse.partition_pos law halfTrace
    halfTrace_measurable halfTrace_bound β
  have hden : c * Real.exp (β*(1-δ/2)) ≤ z := partition_lower δ β hβ
  have hnum : n ≤ Real.exp (β*(1-δ)) := lower_integral_upper δ β hβ
  rw [tilted_lowerCap_mass]
  change n / z ≤ Real.exp (-(β*δ/2)) / c
  apply (div_le_div_iff₀ hz hc).mpr
  calc
    n * c ≤ Real.exp (β*(1-δ)) * c := mul_le_mul_of_nonneg_right hnum hc.le
    _ = Real.exp (-(β*δ/2)) * (c * Real.exp (β*(1-δ/2))) := by
      calc
        Real.exp (β*(1-δ)) * c = c * Real.exp (β*(1-δ)) := mul_comm _ _
        _ = c * Real.exp (-(β*δ/2) + β*(1-δ/2)) := by congr 1; ring
        _ = Real.exp (-(β*δ/2)) * (c * Real.exp (β*(1-δ/2))) := by
          rw [Real.exp_add]
          ring
    _ ≤ Real.exp (-(β*δ/2)) * z :=
      mul_le_mul_of_nonneg_left hden (Real.exp_pos _).le



private theorem tail_tendsto_zero (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun β : ℝ =>
      (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).real (lowerCap δ))
      atTop (𝓝 0) := by
  let c := law.real (upperCap δ)
  have hc : 0 < c := upperCap_mass_pos δ hδ
  have hneg : -(δ/2) < 0 := by linarith
  have ht : Tendsto (fun β : ℝ => Real.exp ((-(δ/2))*β)) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hneg)
  have hupper : Tendsto (fun β : ℝ => Real.exp (-(β*δ/2))/c) atTop (𝓝 0) := by
    convert ht.div_const c using 1 <;> simp [show (0:ℝ)/c=0 by simp]
    funext β
    congr 1
    ring
  apply squeeze_zero' (Eventually.of_forall (fun β => measureReal_nonneg)) ?_ hupper
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
  exact tilted_lowerCap_bound δ β hδ hβ




private theorem mean_defect_bound (δ β : ℝ) (hδ : 0 ≤ δ) :
    1 - (∫ A, halfTrace A ∂BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) ≤
      δ + 2 * (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).real
        (lowerCap δ) := by
  let μ := BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β
  let f : SU2 → ℝ := (lowerCap δ).indicator (fun _ => 1)
  letI : IsProbabilityMeasure μ :=
    BoundedExponentialTiltResponse.tiltedMeasure_probability law halfTrace
      halfTrace_measurable halfTrace_bound β
  have hs : MeasurableSet (lowerCap δ) :=
    measurableSet_le halfTrace_measurable measurable_const
  have hiX : Integrable halfTrace μ := by
    apply Integrable.mono' (integrable_const (1:ℝ)) halfTrace_measurable.aestronglyMeasurable
    filter_upwards with A
    simpa only [Real.norm_eq_abs] using halfTrace_bound A
  have hif : Integrable f μ := by
    apply Integrable.mono' (integrable_const (1:ℝ))
      (measurable_const.indicator hs).aestronglyMeasurable
    filter_upwards with A
    by_cases hA : A ∈ lowerCap δ <;> simp [f, hA]
  have hpoint (A : SU2) : 1-halfTrace A ≤ δ + 2*f A := by
    by_cases hA : A ∈ lowerCap δ
    · have hx := halfTrace_bound A
      simp [f, hA]
      linarith [abs_le.mp hx]
    · have hx : 1-δ < halfTrace A := lt_of_not_ge (by simpa [lowerCap] using hA)
      simp [f, hA]
      linarith
  have hm := integral_mono (μ := μ) ((integrable_const (1:ℝ)).sub hiX)
    ((integrable_const δ).add (hif.const_mul 2)) hpoint
  have hfint : (∫ A, f A ∂μ) = μ.real (lowerCap δ) := integral_indicator_one hs
  change (∫ A, (1-halfTrace A) ∂μ) ≤ (∫ A, (δ+2*f A) ∂μ) at hm
  rw [integral_sub (integrable_const (1:ℝ)) hiX,
    integral_add (integrable_const δ) (hif.const_mul 2),
    integral_const_mul] at hm
  simpa [hfint] using hm

private theorem mean_le_one (β : ℝ) :
    (∫ A, halfTrace A ∂BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β) ≤ 1 := by
  let μ := BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β
  letI : IsProbabilityMeasure μ :=
    BoundedExponentialTiltResponse.tiltedMeasure_probability law halfTrace
      halfTrace_measurable halfTrace_bound β
  have hiX : Integrable halfTrace μ := by
    apply Integrable.mono' (integrable_const (1:ℝ)) halfTrace_measurable.aestronglyMeasurable
    filter_upwards with A
    simpa only [Real.norm_eq_abs] using halfTrace_bound A
  have hm := integral_mono hiX (integrable_const (1:ℝ))
    (fun A => (abs_le.mp (halfTrace_bound A)).2)
  simpa [μ] using hm

theorem positive_mean_tendsto_one : Tendsto
    (fun β : ℝ => ∫ A, halfTrace A ∂BoundedExponentialTiltResponse.tiltedMeasure law
      halfTrace β) atTop (𝓝 1) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let δ : ℝ := (1-a)/2
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hsmall : 0 < (1-a)/4 := by linarith
    have ht := (tendsto_order.mp (tail_tendsto_zero δ hδ)).2 ((1-a)/4) hsmall
    filter_upwards [ht] with β htail
    have hb := mean_defect_bound δ β hδ.le
    change (BoundedExponentialTiltResponse.tiltedMeasure law halfTrace β).real
      (lowerCap δ) < (1-a)/4 at htail
    dsimp [δ] at hb
    linarith
  · intro b hb
    exact Eventually.of_forall (fun β => lt_of_le_of_lt (mean_le_one β) hb)


private theorem halfTrace_minus (B : SU2) :
    halfTrace (SU2StapleExtremes.minusOne * B) = -halfTrace B := by
  simp [halfTrace, SU2StapleExtremes.minusOne,
    QuaternionSU2Representation.hom, QuaternionSU2Representation.repr,
    SU2TraceHessianModel.traceReal, Matrix.trace_fin_two, Matrix.mul_apply, Matrix.vecMul, Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_two]
  ring




private theorem partition_even (β : ℝ) :
    BoundedExponentialTiltResponse.partition law halfTrace (-β) =
      BoundedExponentialTiltResponse.partition law halfTrace β := by
  have he := integral_mul_left_eq_self (μ := law)
    (fun A : SU2 => Real.exp (β*halfTrace A)) SU2StapleExtremes.minusOne
  simp only [BoundedExponentialTiltResponse.partition,
    BoundedExponentialTiltResponse.weighted, one_mul] at he ⊢
  simpa only [halfTrace_minus, mul_neg, neg_mul] using he

private theorem weighted_odd (β : ℝ) :
    BoundedExponentialTiltResponse.weighted law halfTrace halfTrace (-β) =
      -BoundedExponentialTiltResponse.weighted law halfTrace halfTrace β := by
  have he := integral_mul_left_eq_self (μ := law)
    (fun A : SU2 => halfTrace A * Real.exp ((-β)*halfTrace A))
    SU2StapleExtremes.minusOne
  have hf : (fun A : SU2 => halfTrace (SU2StapleExtremes.minusOne*A) *
      Real.exp ((-β)*halfTrace (SU2StapleExtremes.minusOne*A))) =
      (fun A => -(halfTrace A * Real.exp (β*halfTrace A))) := by
    funext A
    rw [halfTrace_minus]
    ring
  rw [hf, integral_neg] at he
  change _ = _
  exact he.symm




private theorem expectation_odd (β : ℝ) :
    BoundedExponentialTiltResponse.expectation law halfTrace halfTrace (-β) =
      -BoundedExponentialTiltResponse.expectation law halfTrace halfTrace β := by
  unfold BoundedExponentialTiltResponse.expectation
  rw [weighted_odd, partition_even]
  ring

theorem central_mean_odd (β : ℝ) :
    (∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β
      SU2StapleExtremes.minusOne) =
      -(∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β (1 : SU2)) := by
  rw [SU2OneWordBoundaryInfluence.minus_law,
    BoundedExponentialTiltResponse.tilted_integral law halfTrace halfTrace
      halfTrace_measurable halfTrace_bound,
    expectation_odd,
    SU2OneWordTransfer.transition_identity_law,
    BoundedExponentialTiltResponse.tilted_integral law halfTrace halfTrace
      halfTrace_measurable halfTrace_bound]

theorem plus_mean_tendsto_one : Tendsto
    (fun β : ℝ => ∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β (1 : SU2))
      atTop (𝓝 1) := by
  have he : (fun β : ℝ => ∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β (1 : SU2)) =
      (fun β : ℝ => ∫ A, halfTrace A ∂BoundedExponentialTiltResponse.tiltedMeasure law
        halfTrace β) := by
    funext β
    rw [SU2OneWordTransfer.transition_identity_law]
  rw [he]
  exact positive_mean_tendsto_one

theorem minus_mean_tendsto_neg_one : Tendsto
    (fun β : ℝ => ∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β
      SU2StapleExtremes.minusOne) atTop (𝓝 (-1)) := by
  have he : (fun β : ℝ => ∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β
      SU2StapleExtremes.minusOne) =
      (fun β : ℝ => -(∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β (1 : SU2))) := by
    funext β
    exact central_mean_odd β
  rw [he]
  exact plus_mean_tendsto_one.neg

theorem no_uniform_central_mean_contraction (q : ℝ) (hq : q < 1) :
    ∃ β : ℝ, 0 ≤ β ∧ 2*q <
      (∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β (1 : SU2)) -
      (∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β
        SU2StapleExtremes.minusOne) := by
  have hd : Tendsto (fun β : ℝ =>
      (∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β (1 : SU2)) -
      (∫ A, halfTrace A ∂SU2OneWordTransfer.transition law β
        SU2StapleExtremes.minusOne)) atTop (𝓝 2) := by
    convert plus_mean_tendsto_one.sub minus_mean_tendsto_neg_one using 1 <;> norm_num
  have hev := (tendsto_order.mp hd).1 (2*q) (by linarith)
  obtain ⟨β, hβ, hh⟩ := (eventually_ge_atTop (0:ℝ) |>.and hev).exists
  exact ⟨β, hβ, hh⟩

end OperatorDerivativeRewrite.Foundation.SU2OneWordLargeCoupling
