import Foundation.PeriodicBridgeExchangeObstruction
/-! Actual normalized second response along the Wilson endpoint rotation.
The curve acceleration and both normalization derivatives must be retained. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicEndpointSecondResponse
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicEndpointScore
open PeriodicSlabGauge
attribute [local irreducible] kernel boundaryHaar gaugeHaar spatialAction temporalAction

private def acceleration (β : ℝ) (U W : State) (h : ℝ) (q : Space) : ℝ :=
  -β * traceSum (left h U) (right h W) q

private theorem slope_measurable (β : ℝ) (U W : State) (h : ℝ) :
    Measurable (phaseSlope β U W h) := by
  unfold phaseSlope
  exact (((traceSum_measurable U W).const_mul _).add
    ((traceSum_measurable _ _).const_mul _)).const_mul _

private theorem acceleration_measurable (β : ℝ) (U W : State) (h : ℝ) :
    Measurable (acceleration β U W h) := (traceSum_measurable _ _).const_mul _

private theorem acceleration_bound (β : ℝ) (U W : State) (h : ℝ) (q : Space) :
    |acceleration β U W h q| ≤ 384 * |β| := by
  unfold acceleration
  rw [abs_mul, abs_neg]
  exact (mul_le_mul_of_nonneg_left (traceSum_bound _ _ q) (abs_nonneg β)).trans_eq (by ring)

private theorem slope_derivative (β : ℝ) (U W : State) (h : ℝ) (q : Space) :
    HasDerivAt (fun t => phaseSlope β U W t q) (acceleration β U W h q) h := by
  have hd := ((((Real.hasDerivAt_sin h).neg).mul_const (traceSum U W q)).add
    ((Real.hasDerivAt_cos h).mul_const
      (traceSum (left (Real.pi/2) U) (right (Real.pi/2) W) q))).const_mul β
  unfold acceleration
  rw [traceSum_rotation]
  unfold phaseSlope
  convert hd using 1 <;> ring

private def firstWeighted (β : ℝ) (U W : State) (f : Space → ℝ) (h : ℝ) : ℝ :=
  ∫ q, f q * Real.exp (phase β U W h q) * phaseSlope β U W h q
    ∂PeriodicAugmentedBridge.law β U W

private theorem weighted_derivative (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) (t : ℝ) :
    HasDerivAt (weighted β U W f) (firstWeighted β U W f t) t := by
  let μ := PeriodicAugmentedBridge.law β U W
  let F := fun h q => f q * Real.exp (phase β U W h q)
  let G := fun h q => f q * Real.exp (phase β U W h q) * phaseSlope β U W h q
  let E := Real.exp (1152 * |β|)
  have he (h : ℝ) (q : Space) : Real.exp (phase β U W h q) ≤ E :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β U W h q))
  have hm (h : ℝ) : AEStronglyMeasurable (F h) μ :=
    (hf.mul (phase_measurable β U W h).exp).aestronglyMeasurable
  have hi : Integrable (F t) μ := by
    apply Integrable.of_bound (hm t) (M*E)
    filter_upwards with q
    change ‖f q * Real.exp (phase β U W t q)‖ ≤ _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hb q) (he t q) (Real.exp_pos _).le hM
  have hg : AEStronglyMeasurable (G t) μ :=
    ((hf.mul (phase_measurable β U W t).exp).mul (slope_measurable β U W t)).aestronglyMeasurable
  have hbG : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), ‖G h q‖ ≤ M*E*(768*|β|) := by
    filter_upwards with q h _
    change ‖f q * Real.exp (phase β U W h q) * phaseSlope β U W h q‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hb q) (he h q) (Real.exp_pos _).le hM)
      (phaseSlope_bound β U W h q) (abs_nonneg _)
      (mul_nonneg hM (Real.exp_pos _).le)
  have hd : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), HasDerivAt (F · q) (G h q) h := by
    filter_upwards with q h _
    simpa only [F, G, Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
      (phase_hasDerivAt β U W h q).exp.const_mul (f q)
  obtain ⟨_, hh⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall hm) hi hg hbG
    (integrable_const _) hd
  exact hh

private theorem firstWeighted_derivative (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) (t : ℝ) :
    HasDerivAt (firstWeighted β U W f)
      (∫ q, f q * Real.exp (phase β U W t q) *
        ((phaseSlope β U W t q)^2 + acceleration β U W t q)
        ∂PeriodicAugmentedBridge.law β U W) t := by
  let μ := PeriodicAugmentedBridge.law β U W
  let F := fun h q => f q * Real.exp (phase β U W h q) * phaseSlope β U W h q
  let G := fun h q => f q * Real.exp (phase β U W h q) *
    ((phaseSlope β U W h q)^2 + acceleration β U W h q)
  let E := Real.exp (1152 * |β|)
  let B := 768 * |β|
  have he (h : ℝ) (q : Space) : Real.exp (phase β U W h q) ≤ E :=
    Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β U W h q))
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (abs_nonneg _)
  have hm (h : ℝ) : AEStronglyMeasurable (F h) μ :=
    ((hf.mul (phase_measurable β U W h).exp).mul (slope_measurable β U W h)).aestronglyMeasurable
  have hi : Integrable (F t) μ := by
    apply Integrable.of_bound (hm t) (M*E*B)
    filter_upwards with q
    change ‖f q * Real.exp (phase β U W t q) * phaseSlope β U W t q‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hb q) (he t q) (Real.exp_pos _).le hM)
      (phaseSlope_bound β U W t q) (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
  have hg : AEStronglyMeasurable (G t) μ :=
    ((hf.mul (phase_measurable β U W t).exp).mul
      (((slope_measurable β U W t).pow_const 2).add
        (acceleration_measurable β U W t))).aestronglyMeasurable
  have hq (h : ℝ) (q : Space) :
      |(phaseSlope β U W h q)^2 + acceleration β U W h q| ≤ B^2+B := by
    have hs := phaseSlope_bound β U W h q
    have ha := acceleration_bound β U W h q
    have hp : (phaseSlope β U W h q)^2 ≤ B^2 := by
      simpa only [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hB).2 (show |phaseSlope β U W h q| ≤ B from hs)
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg _)]
    dsimp only [B] at *
    linarith [abs_nonneg β]
  have hbG : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), ‖G h q‖ ≤ M*E*(B^2+B) := by
    filter_upwards with q h _
    change ‖f q * Real.exp (phase β U W h q) * _‖ ≤ _
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (mul_le_mul (hb q) (he h q) (Real.exp_pos _).le hM)
      (hq h q) (abs_nonneg _) (mul_nonneg hM (Real.exp_pos _).le)
  have hd : ∀ᵐ q ∂μ, ∀ h ∈ Set.Ioo (t-1) (t+1), HasDerivAt (F · q) (G h q) h := by
    filter_upwards with q h _
    have hh := ((phase_hasDerivAt β U W h q).exp.const_mul (f q)).mul
      (slope_derivative β U W h q)
    convert hh using 1 <;> dsimp [F, G] <;> ring
  obtain ⟨_, hh⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds (by linarith) (by linarith)) (Eventually.of_forall hm) hi hg hbG
    (integrable_const _) hd
  exact hh

private theorem weighted_one_positive (β : ℝ) (U W : State) (h : ℝ) :
    0 < weighted β U W (fun _ => 1) h := by
  let μ := PeriodicAugmentedBridge.law β U W
  have hi : Integrable (fun q => Real.exp (phase β U W h q)) μ := by
    apply Integrable.of_bound (phase_measurable β U W h).exp.aestronglyMeasurable
      (Real.exp (1152*|β|))
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (phase_bound β U W h q))
  change 0 < ∫ q, 1 * Real.exp (phase β U W h q) ∂μ
  simp only [one_mul]
  apply (integral_pos_iff_support_of_nonneg (fun q => (Real.exp_pos _).le) hi).mpr
  have hs : Function.support (fun q => Real.exp (phase β U W h q)) = Set.univ := by
    ext q
    simp [Function.mem_support, Real.exp_ne_zero]
  rw [hs]
  simp [μ]

/-- Unnormalized second density coefficient: square of the first phase slope
MINUS the actual endpoint-curve acceleration term. -/
def rawCurvature (β : ℝ) (U W : State) (q : Space) : ℝ :=
  (β * direction U W q)^2 - β * traceSum U W q

/-- Both normalization derivatives are retained. This is the second derivative
of the normalized relative density, not the square of the physical first score. -/
def secondScore (β : ℝ) (U W : State) (q : Space) : ℝ :=
  let m := ∫ z, β * direction U W z ∂PeriodicAugmentedBridge.law β U W
  rawCurvature β U W q - 2*m*(β * direction U W q) + 2*m^2 -
    ∫ z, rawCurvature β U W z ∂PeriodicAugmentedBridge.law β U W

theorem rawCurvature_measurable (β : ℝ) (U W : State) : Measurable (rawCurvature β U W) := by
  unfold rawCurvature direction
  exact (((traceSum_measurable _ _).const_mul β).pow_const 2).sub
    ((traceSum_measurable U W).const_mul β)

theorem rawCurvature_bound (β : ℝ) (U W : State) (q : Space) :
    |rawCurvature β U W q| ≤ (384*|β|)^2 + 384*|β| := by
  have hr : |β * direction U W q| ≤ 384*|β| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (traceSum_bound _ _ q) (abs_nonneg β)).trans_eq (by ring)
  have hc : |β * traceSum U W q| ≤ 384*|β| := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (traceSum_bound _ _ q) (abs_nonneg β)).trans_eq (by ring)
  unfold rawCurvature
  apply (abs_sub _ _).trans
  rw [abs_of_nonneg (sq_nonneg _)]
  have hp := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 384*|β|)).2 hr
  rw [sq_abs] at hp
  linarith

private theorem bounded_integrable (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hb : ∀ q, |f q| ≤ M) :
    Integrable f (PeriodicAugmentedBridge.law β U W) :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using hb q))

private theorem firstWeighted_zero (β : ℝ) (U W : State) (f : Space → ℝ) :
    firstWeighted β U W f 0 =
      ∫ q, f q * (β * direction U W q) ∂PeriodicAugmentedBridge.law β U W := by
  simp only [firstWeighted, phase, phaseSlope, direction, Real.cos_zero, Real.sin_zero,
    sub_self, zero_mul, mul_zero, add_zero, zero_add, neg_zero, Real.exp_zero,
    mul_one, one_mul]

private theorem firstWeighted_derivative_zero (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) :
    HasDerivAt (firstWeighted β U W f)
      (∫ q, f q * rawCurvature β U W q ∂PeriodicAugmentedBridge.law β U W) 0 := by
  have hd := firstWeighted_derivative β U W f hf M hM hb 0
  have ha (q : Space) : acceleration β U W 0 q = -β * traceSum U W q := by
    unfold acceleration
    rw [traceSum_rotation]
    simp only [Real.cos_zero, Real.sin_zero, one_mul, zero_mul, add_zero]
  simpa only [phase, phaseSlope, ha, rawCurvature, direction,
    Real.cos_zero, Real.sin_zero, sub_self, zero_mul, mul_zero, add_zero, zero_add,
    neg_zero, Real.exp_zero, mul_one, one_mul, mul_neg, neg_mul, sub_eq_add_neg] using hd

private def ratioSlope (β : ℝ) (U W : State) (f : Space → ℝ) (h : ℝ) : ℝ :=
  (firstWeighted β U W f h * weighted β U W (fun _ => 1) h -
    weighted β U W f h * firstWeighted β U W (fun _ => 1) h) /
      (weighted β U W (fun _ => 1) h)^2

private theorem ratio_derivative (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) (t : ℝ) :
    HasDerivAt (fun h => weighted β U W f h / weighted β U W (fun _ => 1) h)
      (ratioSlope β U W f t) t :=
  (weighted_derivative β U W f hf M hM hb t).div
    (weighted_derivative β U W (fun _ => 1) measurable_const 1 (by norm_num) (fun _ => by norm_num) t)
    (weighted_one_positive β U W t).ne'

private theorem score_pairing_expansion (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) :
    (∫ q, f q * secondScore β U W q ∂PeriodicAugmentedBridge.law β U W) =
      (∫ q, f q * rawCurvature β U W q ∂PeriodicAugmentedBridge.law β U W) -
      2 * (∫ q, β * direction U W q ∂PeriodicAugmentedBridge.law β U W) *
        (∫ q, f q * (β * direction U W q) ∂PeriodicAugmentedBridge.law β U W) +
      (2 * (∫ q, β * direction U W q ∂PeriodicAugmentedBridge.law β U W)^2 -
        ∫ q, rawCurvature β U W q ∂PeriodicAugmentedBridge.law β U W) *
          (∫ q, f q ∂PeriodicAugmentedBridge.law β U W) := by
  let μ := PeriodicAugmentedBridge.law β U W
  let m := ∫ q, β * direction U W q ∂μ
  let n := ∫ q, rawCurvature β U W q ∂μ
  have hfi := bounded_integrable β U W f hf M hb
  have hfr : Integrable (fun q => f q * (β * direction U W q)) μ := by
    apply bounded_integrable β U W _
      (hf.mul ((traceSum_measurable _ _).const_mul β)) (M*(384*|β|))
    intro q
    change |f q * (β * direction U W q)| ≤ _
    rw [abs_mul]
    have hr : |β * direction U W q| ≤ 384*|β| := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (traceSum_bound _ _ q) (abs_nonneg β)).trans_eq (by ring)
    exact mul_le_mul (hb q) hr (abs_nonneg _) hM
  have hfq : Integrable (fun q => f q * rawCurvature β U W q) μ := by
    apply bounded_integrable β U W _ (hf.mul (rawCurvature_measurable β U W))
      (M*((384*|β|)^2+384*|β|))
    intro q
    change |f q * rawCurvature β U W q| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hb q) (rawCurvature_bound β U W q) (abs_nonneg _) hM
  have he : (fun q => f q * secondScore β U W q) =
      (fun q => (f q * rawCurvature β U W q - (2*m)*(f q*(β*direction U W q))) +
        (2*m^2-n)*f q) := by
    funext q
    dsimp only [secondScore, m, n, μ]
    ring
  have hsum := integral_add (hfq.sub (hfr.const_mul (2*m))) (hfi.const_mul (2*m^2-n))
  have hsub := integral_sub hfq (hfr.const_mul (2*m))
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply] at hsum hsub
  rw [he, hsum, hsub, integral_const_mul, integral_const_mul]

private theorem ratioSlope_derivative (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) :
    HasDerivAt (ratioSlope β U W f)
      (∫ q, f q * secondScore β U W q ∂PeriodicAugmentedBridge.law β U W) 0 := by
  have hN := weighted_derivative β U W f hf M hM hb 0
  have hZ := weighted_derivative β U W (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num) 0
  have hNp := firstWeighted_derivative_zero β U W f hf M hM hb
  have hZp := firstWeighted_derivative_zero β U W (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num)
  have hz : weighted β U W (fun _ => 1) 0 = 1 := by rw [weighted_zero]; simp
  have hh := ((hNp.mul hZ).sub (hN.mul hZp)).div (hZ.pow 2)
    (by change (weighted β U W (fun _ => 1) 0)^2 ≠ 0; rw [hz]; norm_num)
  change HasDerivAt (ratioSlope β U W f) _ 0 at hh
  rw [score_pairing_expansion β U W f hf M hM hb]
  convert hh using 1
  simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, hz, weighted_zero,
    firstWeighted_zero, one_mul, mul_one, one_pow, div_one, Nat.reduceSub]
  ring

/-- Actual second derivative, on the bounded measurable augmented core, with
the ORIGINAL normalized Wilson law and both normalizer derivative terms. -/
theorem expectation_second_derivative (β : ℝ) (U W : State) (f : Space → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ q, |f q| ≤ M) :
    HasDerivAt (deriv (fun h => ∫ q, f q
      ∂PeriodicAugmentedBridge.law β (left h U) (right h W)))
      (∫ q, f q * secondScore β U W q ∂PeriodicAugmentedBridge.law β U W) 0 := by
  have he : (fun h => ∫ q, f q ∂PeriodicAugmentedBridge.law β (left h U) (right h W)) =
      (fun h => weighted β U W f h / weighted β U W (fun _ => 1) h) :=
    funext (fun h => rotated_integral β U W h f)
  rw [he]
  have hd : deriv (fun h => weighted β U W f h / weighted β U W (fun _ => 1) h) =
      ratioSlope β U W f := funext (fun h => (ratio_derivative β U W f hf M hM hb h).deriv)
  rw [hd]
  exact ratioSlope_derivative β U W f hf M hM hb

private theorem linear_bound (β : ℝ) (U W : State) (q : Space) :
    |β * direction U W q| ≤ 384*|β| := by
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (traceSum_bound _ _ q) (abs_nonneg β)).trans_eq (by ring)

private theorem mean_linear_bound (β : ℝ) (U W : State) :
    |∫ q, β * direction U W q ∂PeriodicAugmentedBridge.law β U W| ≤ 384*|β| := by
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := PeriodicAugmentedBridge.law β U W)
      (f := fun q => β * direction U W q) (C := 384*|β|)
      (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using linear_bound β U W q))

theorem secondScore_measurable (β : ℝ) (U W : State) : Measurable (secondScore β U W) := by
  unfold secondScore direction
  exact (((rawCurvature_measurable β U W).sub
    (((traceSum_measurable _ _).const_mul β).const_mul _)).add measurable_const).sub measurable_const

theorem secondScore_bound (β : ℝ) (U W : State) (q : Space) :
    |secondScore β U W q| ≤ 6*(384*|β|)^2 + 2*(384*|β|) := by
  let B := 384*|β|
  let m := ∫ z, β * direction U W z ∂PeriodicAugmentedBridge.law β U W
  let n := ∫ z, rawCurvature β U W z ∂PeriodicAugmentedBridge.law β U W
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hm : |m| ≤ B := mean_linear_bound β U W
  have hr : |β * direction U W q| ≤ B := linear_bound β U W q
  have hn : |n| ≤ B^2+B := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (μ := PeriodicAugmentedBridge.law β U W)
        (f := rawCurvature β U W) (C := B^2+B)
        (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using rawCurvature_bound β U W z))
  have hq : |rawCurvature β U W q| ≤ B^2+B := rawCurvature_bound β U W q
  have hmr : |2*m*(β*direction U W q)| ≤ 2*B^2 := by
    have hh := mul_le_mul hm hr (abs_nonneg _) hB
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    nlinarith only [hh]
  have hm2 : |2*m^2| ≤ 2*B^2 := by
    have hh := (sq_le_sq₀ (abs_nonneg _) hB).2 hm
    rw [sq_abs] at hh
    rw [abs_of_nonneg (by positivity : 0 ≤ 2*m^2)]
    linarith
  have h1 := (abs_sub (rawCurvature β U W q) (2*m*(β*direction U W q))).trans
    (add_le_add hq hmr)
  have h2 := (abs_add_le (rawCurvature β U W q-2*m*(β*direction U W q)) (2*m^2)).trans
    (add_le_add h1 hm2)
  have h3 := (abs_sub (rawCurvature β U W q-2*m*(β*direction U W q)+2*m^2) n).trans
    (add_le_add h2 hn)
  change |rawCurvature β U W q-2*m*(β*direction U W q)+2*m^2-n| ≤ 6*B^2+2*B
  linarith only [h3]

theorem secondScore_memLp (β : ℝ) (U W : State) :
    MemLp (secondScore β U W) 2 (PeriodicAugmentedBridge.law β U W) :=
  MemLp.of_bound (secondScore_measurable β U W).aestronglyMeasurable _
    (ae_of_all _ (fun q => by simpa only [Real.norm_eq_abs] using secondScore_bound β U W q))

/-- The genuine physical second coefficient is a CONDITIONAL second score.
It is not the square of the conditional first score. -/
def physicalSecond (β : ℝ) (U W : State) (V : State) : ℝ :=
  ∫ ab, secondScore β U W (V,ab) ∂PeriodicPhysicalBridgeScore.auxiliaryLaw β U W V

theorem physicalSecond_measurable (β : ℝ) (U W : State) : Measurable (physicalSecond β U W) := by
  have he : physicalSecond β U W = (fun V =>
      (∫ ab, PeriodicAugmentedBridge.density β U W (V,ab) * secondScore β U W (V,ab)
        ∂PeriodicPhysicalBridgeScore.temporalReference) / PeriodicGroundBridge.bridgeWeight β U W V) := by
    funext V
    exact PeriodicPhysicalBridgeScore.auxiliary_integral β U W V _
  rw [he]
  exact ((PeriodicAugmentedBridge.density_measurable β U W).mul
    (secondScore_measurable β U W)).stronglyMeasurable.integral_prod_right.measurable.div
      (PeriodicGroundBridge.bridgeWeight_measurable β U W)

theorem physicalSecond_bound (β : ℝ) (U W V : State) :
    |physicalSecond β U W V| ≤ 6*(384*|β|)^2+2*(384*|β|) := by
  letI := PeriodicPhysicalBridgeScore.auxiliary_probability β U W V
  simpa only [physicalSecond, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := PeriodicPhysicalBridgeScore.auxiliaryLaw β U W V)
      (f := fun ab => secondScore β U W (V,ab)) (C := 6*(384*|β|)^2+2*(384*|β|))
      (ae_of_all _ (fun ab => by simpa only [Real.norm_eq_abs] using secondScore_bound β U W (V,ab)))

theorem physicalSecond_memLp (β : ℝ) (U W : State) :
    MemLp (physicalSecond β U W) 2 (PeriodicGroundBridge.law β U W) :=
  MemLp.of_bound (physicalSecond_measurable β U W).aestronglyMeasurable _
    (ae_of_all _ (fun V => by simpa only [Real.norm_eq_abs] using physicalSecond_bound β U W V))

/-- Actual original-law conditional duality for the second coefficient. -/
theorem physicalSecond_pairing (β : ℝ) (U W : State) (f : State → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    (∫ q, f q.1 * secondScore β U W q ∂PeriodicAugmentedBridge.law β U W) =
      ∫ V, f V * physicalSecond β U W V ∂PeriodicGroundBridge.law β U W := by
  let K := 6*(384*|β|)^2+2*(384*|β|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hi : Integrable (fun q : Space =>
      PeriodicAugmentedBridge.density β U W q * (f q.1 * secondScore β U W q))
        PeriodicAugmentedBridge.reference := by
    apply Integrable.of_bound ((PeriodicAugmentedBridge.density_measurable β U W).mul
      ((hf.comp measurable_fst).mul (secondScore_measurable β U W))).aestronglyMeasurable
        ((Real.exp (768*|β|)^2)*(M*K))
    filter_upwards with q
    change ‖PeriodicAugmentedBridge.density β U W q * (f q.1 * secondScore β U W q)‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (PeriodicAugmentedBridge.density_pos β U W q)]
    exact mul_le_mul (PeriodicAugmentedBridge.density_upper β U W q)
      (mul_le_mul (hb q.1) (secondScore_bound β U W q) (abs_nonneg _) hM)
      (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sq_nonneg _)
  rw [PeriodicAugmentedBridge.integral_formula, PeriodicGroundBridge.integral_formula]
  congr 1
  rw [PeriodicAugmentedBridge.reference, integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards with V
  rw [physicalSecond, PeriodicPhysicalBridgeScore.auxiliary_integral]
  have he : (fun ab : Gauge × Gauge => PeriodicAugmentedBridge.density β U W (V,ab) *
      (f V * secondScore β U W (V,ab))) =
      (fun ab => f V * (PeriodicAugmentedBridge.density β U W (V,ab) * secondScore β U W (V,ab))) := by
    funext ab
    ring
  rw [he, integral_const_mul]
  field_simp [(PeriodicGroundBridge.bridgeWeight_pos β U W V).ne']
  rfl

/-- Genuine PHYSICAL second derivative on the actual bounded middle core.
No nonzero second response or reconstruction completeness is asserted. -/
theorem physical_second_derivative (β : ℝ) (U W : State) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    HasDerivAt (deriv (fun h => ∫ V, f V
      ∂PeriodicGroundBridge.law β (left h U) (right h W)))
      (∫ V, f V * physicalSecond β U W V ∂PeriodicGroundBridge.law β U W) 0 := by
  have hd := expectation_second_derivative β U W (fun q => f q.1)
    (hf.comp measurable_fst) M hM (fun q => hb q.1)
  rw [physicalSecond_pairing β U W f hf M hM hb] at hd
  have he : (fun h => ∫ q, f q.1 ∂PeriodicAugmentedBridge.law β (left h U) (right h W)) =
      (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β (left h U) (right h W)) :=
    funext (fun h => PeriodicAugmentedBridge.projection_integral β _ _ f hf M hb)
  rw [he] at hd
  exact hd

/-- The first-order exchange-null direction now has a constructed second
channel in the ORIGINAL law. Its nonvanishing remains a separate obligation. -/
theorem exchange_second_derivative (β : ℝ) (f : State → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ V, |f V| ≤ M) :
    HasDerivAt (deriv (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β
      (PeriodicBridgeExchangeObstruction.path h) (PeriodicBridgeExchangeObstruction.path (-h))))
      (∫ V, f V * physicalSecond β PeriodicEndpointFibreWitness.leftEndpoint
        PeriodicEndpointFibreWitness.leftEndpoint V
        ∂PeriodicGroundBridge.law β PeriodicEndpointFibreWitness.leftEndpoint
          PeriodicEndpointFibreWitness.leftEndpoint) 0 := by
  have hd := physical_second_derivative β PeriodicEndpointFibreWitness.leftEndpoint
    PeriodicEndpointFibreWitness.leftEndpoint f hf M hM hb
  have he : (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β
      (left h PeriodicEndpointFibreWitness.leftEndpoint) (right h PeriodicEndpointFibreWitness.leftEndpoint)) =
      (fun h => ∫ V, f V ∂PeriodicGroundBridge.law β
        (PeriodicBridgeExchangeObstruction.path h) (PeriodicBridgeExchangeObstruction.path (-h))) := by
    funext h
    rw [PeriodicBridgeExchangeObstruction.coherent_law]
  rw [he] at hd
  exact hd

private theorem trace_middle_gauge (g : Gauge) (U W V : State) (ab : Gauge × Gauge) :
    traceSum U W (gaugeAction g V,ab) = traceSum U W (V,(ab.1*g,g⁻¹*ab.2)) := by
  have hr (e : SpatialEdge) :
      halfTrace (temporalWord (gaugeAction g V) W ab.2 e) =
        halfTrace (temporalWord V W (g⁻¹*ab.2) e) := by
    have hh := temporal_left_word g (g⁻¹*ab.2) V W e
    rw [show g*(g⁻¹*ab.2)=ab.2 by group] at hh
    rw [hh, halfTrace_conjugate]
  unfold traceSum
  simp_rw [temporal_right_word, hr]

private theorem second_middle_gauge (β : ℝ) (g : Gauge) (U W V : State) (ab : Gauge × Gauge) :
    secondScore β U W (gaugeAction g V,ab) = secondScore β U W (V,(ab.1*g,g⁻¹*ab.2)) := by
  dsimp only [secondScore, rawCurvature, direction]
  simp only [trace_middle_gauge]

private theorem density_middle_gauge (β : ℝ) (g : Gauge) (U W V : State) (ab : Gauge × Gauge) :
    PeriodicAugmentedBridge.density β U W (gaugeAction g V,ab) =
      PeriodicAugmentedBridge.density β U W (V,(ab.1*g,g⁻¹*ab.2)) := by
  have hr : weight β (gaugeAction g V) W ab.2 = weight β V W (g⁻¹*ab.2) := by
    have hh := weight_left β g (g⁻¹*ab.2) V W
    rw [show g*(g⁻¹*ab.2)=ab.2 by group] at hh
    exact hh
  simp only [PeriodicAugmentedBridge.density, weight_right, hr]

/-- Full middle-vertex gauge invariance, with the endpoint curve held fixed.
This makes no representative-invariance claim for untransported endpoint axes. -/
theorem physicalSecond_gauge (β : ℝ) (g : Gauge) (U W V : State) :
    physicalSecond β U W (gaugeAction g V) = physicalSecond β U W V := by
  rw [physicalSecond, PeriodicPhysicalBridgeScore.auxiliary_integral,
    physicalSecond, PeriodicPhysicalBridgeScore.auxiliary_integral]
  have hn : PeriodicGroundBridge.bridgeWeight β U W (gaugeAction g V) =
      PeriodicGroundBridge.bridgeWeight β U W V := by
    unfold PeriodicGroundBridge.bridgeWeight
    rw [kernel_right_invariant, kernel_left_invariant]
  rw [hn]
  have hh := ((gauge_right_preserving g).prod (gauge_left_preserving g⁻¹)).integral_comp
    ((MeasurableEquiv.mulRight g).prodCongr (MeasurableEquiv.mulLeft g⁻¹)).measurableEmbedding
    (fun ab : Gauge × Gauge => PeriodicAugmentedBridge.density β U W (V,ab) *
      secondScore β U W (V,ab))
  change (∫ ab, PeriodicAugmentedBridge.density β U W (V,(ab.1*g,g⁻¹*ab.2)) *
    secondScore β U W (V,(ab.1*g,g⁻¹*ab.2)) ∂gaugeHaar.prod gaugeHaar) =
    (∫ ab, PeriodicAugmentedBridge.density β U W (V,ab) * secondScore β U W (V,ab)
      ∂gaugeHaar.prod gaugeHaar) at hh
  simp_rw [density_middle_gauge, second_middle_gauge]
  exact congrArg (fun x => x / PeriodicGroundBridge.bridgeWeight β U W V) hh

theorem secondScore_mean_zero (β : ℝ) (U W : State) :
    (∫ q, secondScore β U W q ∂PeriodicAugmentedBridge.law β U W) = 0 := by
  have he := score_pairing_expansion β U W (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num)
  simp only [one_mul, integral_const, probReal_univ, one_smul] at he
  nlinarith only [he]

theorem physicalSecond_mean_zero (β : ℝ) (U W : State) :
    (∫ V, physicalSecond β U W V ∂PeriodicGroundBridge.law β U W) = 0 := by
  have he := physicalSecond_pairing β U W (fun _ => 1) measurable_const 1
    (by norm_num) (fun _ => by norm_num)
  simpa only [one_mul, secondScore_mean_zero] using he.symm

/-- A fixed admissible physical test detects the second channel exactly by
its native squared norm. Strict positivity is NOT inferred from this identity. -/
theorem frozen_second_derivative (β : ℝ) (U W : State) :
    HasDerivAt (deriv (fun h => ∫ V, physicalSecond β U W V
      ∂PeriodicGroundBridge.law β (left h U) (right h W)))
      (∫ V, (physicalSecond β U W V)^2 ∂PeriodicGroundBridge.law β U W) 0 := by
  simpa only [pow_two] using physical_second_derivative β U W (physicalSecond β U W)
    (physicalSecond_measurable β U W) (6*(384*|β|)^2+2*(384*|β|))
    (by positivity) (physicalSecond_bound β U W)

end OperatorDerivativeRewrite.Foundation.PeriodicEndpointSecondResponse
