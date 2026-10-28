import Foundation.SU2SevenLinkGroundTransform
import Foundation.YMResetGroundState

/-! Test of the missing second spatial plaquette. Equal positive weights on
both adjacent plaquettes break the private-link center symmetry used in the
one-weight variational construction. No four-dimensional gap claim is made. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2HomogeneousPlaquetteObstruction
open QuaternionSU2Representation SU2WilsonConvolution SU2SevenLinkTransfer
open SU2SevenLinkParity SU2SevenLinkOddTrial BoundedExponentialTiltResponse

/-- Normalized sum; the actual Boltzmann parameter is 2t. -/
def potential (s : State) : ℝ := (first s+second s)/2

theorem potential_measurable : Measurable potential := (first_measurable.add second_measurable).div_const 2

theorem potential_bound (s : State) : |potential s| ≤ 1 := by
  unfold potential
  rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  have h := (abs_add_le (first s) (second s)).trans (add_le_add (first_bound s) (second_bound s))
  linarith

def weight (t : ℝ) (s : State) : ℝ := Real.exp (t*potential s)

def homogeneousStep (β t : ℝ) (f : State → ℝ) (s : State) : ℝ :=
  weight t s*SU2SevenLinkTransfer.step β (fun r => weight t r*f r) s

theorem potential_flip (s : State) : potential (SU2SevenLinkParity.flip s)=(first s-second s)/2 := by
  unfold potential
  rw [first_flip,second_flip]
  ring

theorem potential_identity : potential (1 : State)=1 := by
  norm_num [potential,first,second,leftPath,rightPath,halfTrace,SU2TraceHessianModel.traceReal,Matrix.trace_fin_two]

theorem potential_flip_identity : potential (SU2SevenLinkParity.flip (1 : State))=0 := by
  rw [potential_flip]
  norm_num [first,second,leftPath,rightPath,halfTrace,SU2TraceHessianModel.traceReal,Matrix.trace_fin_two]

/-- Pointwise failure, at an actual flat configuration, for EVERY nonzero tilt. -/
theorem weight_not_flip_invariant (t : ℝ) (ht : t ≠ 0) :
    weight t (SU2SevenLinkParity.flip (1 : State)) ≠ weight t (1 : State) := by
  rw [weight,weight,potential_flip_identity,potential_identity,mul_zero,mul_one,Real.exp_zero]
  intro he
  have h := Real.exp_injective (show Real.exp (0:ℝ)=Real.exp t by simpa using he)
  exact ht h.symm

private theorem product_measurableMul (G H : Type*) [MeasurableSpace G] [MeasurableSpace H]
    [Mul G] [Mul H] [MeasurableMul G] [MeasurableMul H] : MeasurableMul (G × H) where
  measurable_const_mul g := ((measurable_const_mul g.1).comp measurable_fst).prodMk
    ((measurable_const_mul g.2).comp measurable_snd)
  measurable_mul_const g := ((measurable_mul_const g.1).comp measurable_fst).prodMk
    ((measurable_mul_const g.2).comp measurable_snd)

private instance haar_leftInvariant : haar.IsMulLeftInvariant := by
  letI m2 : MeasurableMul (SU2 × SU2) := product_measurableMul _ _
  letI m3 : MeasurableMul (SU2 × SU2 × SU2) := product_measurableMul _ _
  letI m4 : MeasurableMul (SU2 × SU2 × SU2 × SU2) := product_measurableMul _ _
  letI m5 : MeasurableMul (SU2 × SU2 × SU2 × SU2 × SU2) := product_measurableMul _ _
  letI m6 : MeasurableMul (SU2 × SU2 × SU2 × SU2 × SU2 × SU2) := product_measurableMul _ _
  letI h2 : (law.prod law).IsMulLeftInvariant := by infer_instance
  letI h3 : (law.prod (law.prod law)).IsMulLeftInvariant := by infer_instance
  letI h4 : (law.prod (law.prod (law.prod law))).IsMulLeftInvariant := by infer_instance
  letI h5 : (law.prod (law.prod (law.prod (law.prod law)))).IsMulLeftInvariant := by infer_instance
  letI h6 : (law.prod (law.prod (law.prod (law.prod (law.prod law))))).IsMulLeftInvariant := by infer_instance
  letI p6 : IsProbabilityMeasure (law.prod (law.prod (law.prod (law.prod (law.prod law))))) := by infer_instance
  unfold haar edgeLaw
  exact Measure.prod.instIsMulLeftInvariant

theorem noise_zero : noise 0=haar := by
  unfold noise increment
  rw [SU2StapleExtremes.zero_tilt]
  rfl

theorem kinetic_reset (f : State → ℝ) (s : State) :
    SU2SevenLinkTransfer.step 0 f s=∫ r, f r ∂haar := by
  unfold SU2SevenLinkTransfer.step
  rw [noise_zero]
  exact integral_mul_left_eq_self f s

theorem weight_amplitude (t : ℝ) : weight t=YMResetGroundState.amplitude potential (2*t) := by
  funext s
  unfold weight YMResetGroundState.amplitude
  congr 1
  ring

/-- Actual two-spatial-plaquette transfer at the genuine Wilson reset law. -/
theorem homogeneous_reset (t : ℝ) (f : State → ℝ) (s : State) :
    homogeneousStep 0 t f s=YMResetGroundState.transfer haar potential (2*t) f s := by
  unfold homogeneousStep
  rw [kinetic_reset,weight_amplitude]
  rfl

/-- Actual stationary reset law, with BOTH spatial plaquettes in the density. -/
def stationary (t : ℝ) : Measure State := tiltedMeasure haar potential (2*t)

theorem stationary_probability (t : ℝ) : IsProbabilityMeasure (stationary t) :=
  tiltedMeasure_probability haar potential potential_measurable potential_bound _

/-- Exact ground normalization is reused, not assumed. -/
theorem ground_transform (t : ℝ) (f : State → ℝ) (s : State) :
    homogeneousStep 0 t (fun r => weight t r*f r) s/
      (partition haar potential (2*t)*weight t s)=∫ r, f r ∂stationary t := by
  rw [homogeneous_reset,weight_amplitude]
  exact YMResetGroundState.ground_transform haar potential potential_measurable potential_bound (2*t) f s

/-- The homogeneous operator itself does not commute with the old flip, already
at the actual reset coupling. This is not merely a failure of a chosen proof. -/
theorem homogeneous_not_flip_commuting (t : ℝ) (ht : t ≠ 0) :
    homogeneousStep 0 t (fun _ => 1) (SU2SevenLinkParity.flip (1 : State)) ≠
      homogeneousStep 0 t (fun _ => 1) (1 : State) := by
  have hi : 0 < ∫ r, weight t r ∂haar := by
    simpa only [partition,weighted,one_mul,weight] using
      partition_pos haar potential potential_measurable potential_bound t
  unfold homogeneousStep
  simp_rw [kinetic_reset,mul_one]
  exact fun he => weight_not_flip_invariant t ht (mul_right_cancel₀ hi.ne' he)

private theorem haar_second_mean : (∫ s, second s ∂haar)=0 := by
  simpa only [mul_one] using odd_even_orthogonal second (fun _ => 1) second_flip (fun _ => rfl)

private theorem haar_mixed_mean : (∫ s, second s*first s ∂haar)=0 :=
  odd_even_orthogonal second first second_flip first_flip

private theorem second_potential_integral : (∫ s, second s*potential s ∂haar)=(1/8:ℝ) := by
  have h1 : Integrable (fun s => second s*first s) haar := by
    apply Integrable.of_bound (second_measurable.mul first_measurable).aestronglyMeasurable 1
    filter_upwards with s
    change ‖second s*first s‖ ≤ 1
    rw [Real.norm_eq_abs,abs_mul]
    simpa using mul_le_mul (second_bound s) (first_bound s) (abs_nonneg _) (by norm_num)
  have h2 := bounded_power_integrable haar second second_measurable second_bound 2
  have he (s : State) : second s*potential s=(second s*first s+second s^2)/2 := by unfold potential; ring
  simp_rw [he]
  rw [integral_div,integral_add h1 h2,haar_mixed_mean,haar_second_square]
  norm_num

/-- Observable under the ACTUAL ground-normalized homogeneous reset law. -/
def rightMean (t : ℝ) : ℝ := ∫ s, second s ∂stationary t

theorem rightMean_zero : rightMean 0=0 := by
  unfold rightMean stationary
  rw [tilted_integral haar potential second potential_measurable potential_bound,mul_zero,expectation_zero,haar_second_mean]

theorem rightMean_derivative : HasDerivAt rightMean (1/4:ℝ) 0 := by
  have h := expectation_hasDerivAt_zero haar potential second potential_measurable second_measurable
    potential_bound 1 (by norm_num) second_bound
  rw [second_potential_integral,haar_second_mean] at h
  norm_num only [zero_mul,sub_zero] at h
  have h' : HasDerivAt (expectation haar potential second) (1/8:ℝ) (2*(0:ℝ)) := by simpa using h
  have hh := h'.comp 0 ((hasDerivAt_id (0:ℝ)).const_mul 2)
  convert hh using 1
  · funext t
    exact tilted_integral haar potential second potential_measurable potential_bound (2*t)
  · norm_num

/-- The old right-plaquette observable is NOT centered for arbitrarily small
positive homogeneous spatial weights, in a fully realized stationary model. -/
theorem positive_rightMean_near_zero (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ 0 < rightMean t := by
  have h := positive_derivative_arbitrarily_small_increase rightMean (1/4) rightMean_derivative (by norm_num) ε hε
  simpa only [rightMean_zero] using h

/-- The OLD one-weight variational trial paired with the ACTUAL homogeneous
reset vacuum. Its derivative will expose the lost centering directly. -/
def oldTrialOverlap (A B t : ℝ) : ℝ :=
  ∫ s, SU2SevenLinkVariational.unweight t (oddPolynomial t A B) s*weight t s ∂haar

private theorem weighted_integrable (f : State → ℝ) (hf : Measurable f)
    (M r : ℝ) (hb : ∀ s, |f s| ≤ M) :
    Integrable (fun s => f s*Real.exp (r*second s)) haar := by
  have h := (exponential_integrable haar second second_measurable second_bound r).bdd_mul
    hf.aestronglyMeasurable (c := M) (ae_of_all _ (fun s => by simpa only [Real.norm_eq_abs] using hb s))
  simpa only [mul_comm] using h

private theorem haar_meanChannel_mean : (∫ s, meanChannel s ∂haar)=0 := by
  simpa only [mul_one] using odd_even_orthogonal meanChannel (fun _ => 1) meanChannel_flip (fun _ => rfl)

private theorem haar_residual_mean : (∫ s, SU2SevenLinkTransfer.residual s ∂haar)=0 := by
  simpa only [mul_one] using odd_even_orthogonal SU2SevenLinkTransfer.residual (fun _ => 1) residual_flip (fun _ => rfl)

theorem oldTrialOverlap_formula (A B t : ℝ) :
    oldTrialOverlap A B t=weighted haar second second (t/2)+
      (t*A)*weighted haar second meanChannel (t/2)+(t*B)*weighted haar second SU2SevenLinkTransfer.residual (t/2) := by
  have hY := weighted_integrable second second_measurable 1 (t/2) second_bound
  have hM := weighted_integrable meanChannel meanChannel_measurable 1 (t/2) meanChannel_bound
  have hQ := weighted_integrable SU2SevenLinkTransfer.residual residual_measurable 2 (t/2) residual_bound
  have he (s : State) : SU2SevenLinkVariational.unweight t (oddPolynomial t A B) s*weight t s=
      (second s*Real.exp ((t/2)*second s)+(t*A)*(meanChannel s*Real.exp ((t/2)*second s)))+
        (t*B)*(SU2SevenLinkTransfer.residual s*Real.exp ((t/2)*second s)) := by
    unfold SU2SevenLinkVariational.unweight weight potential
    have hh : Real.exp (-t*first s/2)*oddPolynomial t A B s*Real.exp (t*((first s+second s)/2))=
        oddPolynomial t A B s*Real.exp ((t/2)*second s) := by
      calc
        _ = oddPolynomial t A B s*(Real.exp (-t*first s/2)*Real.exp (t*((first s+second s)/2))) := by ring
        _ = _ := by
          rw [← Real.exp_add,show -t*first s/2+t*((first s+second s)/2)=(t/2)*second s by ring]
    rw [hh,oddPolynomial_pointwise]
    ring
  unfold oldTrialOverlap
  simp_rw [he]
  have houter := integral_add (hY.add (hM.const_mul (t*A))) (hQ.const_mul (t*B))
  have hinner := integral_add hY (hM.const_mul (t*A))
  simp only [Pi.add_apply] at houter hinner
  rw [houter,hinner,integral_const_mul,integral_const_mul]
  rfl

theorem oldTrialOverlap_zero (A B : ℝ) : oldTrialOverlap A B 0=0 := by
  rw [oldTrialOverlap_formula]
  simp only [zero_mul,zero_div,weighted_zero,haar_second_mean,zero_add,add_zero]

/-- Every fixed real correction pair loses orthogonality at FIRST order, even
though the earlier one-weight orthogonality was exact at every tilt. -/
theorem oldTrialOverlap_derivative (A B : ℝ) : HasDerivAt (oldTrialOverlap A B) (1/8:ℝ) 0 := by
  have hY := weighted_hasDerivAt_zero haar second second second_measurable second_measurable
    second_bound 1 (by norm_num) second_bound
  simp_rw [← pow_two] at hY
  rw [haar_second_square] at hY
  have hM := weighted_hasDerivAt_zero haar second meanChannel second_measurable meanChannel_measurable
    second_bound 1 (by norm_num) meanChannel_bound
  have hQ := weighted_hasDerivAt_zero haar second SU2SevenLinkTransfer.residual second_measurable residual_measurable
    second_bound 2 (by norm_num) residual_bound
  have hm0 : (∫ s, meanChannel s*second s ∂haar)=0 := by simpa only [mul_comm] using haar_second_meanChannel
  have hq0 : (∫ s, SU2SevenLinkTransfer.residual s*second s ∂haar)=0 := by simpa only [mul_comm] using haar_second_residual
  rw [hm0] at hM
  rw [hq0] at hQ
  have hy' : HasDerivAt (weighted haar second second) (1/4:ℝ) ((0:ℝ)/2) := by simpa using hY
  have hm' : HasDerivAt (weighted haar second meanChannel) 0 ((0:ℝ)/2) := by simpa using hM
  have hq' : HasDerivAt (weighted haar second SU2SevenLinkTransfer.residual) 0 ((0:ℝ)/2) := by simpa using hQ
  have hhalf := (hasDerivAt_id (0:ℝ)).div_const 2
  have h := ((hy'.comp 0 hhalf).add (((hasDerivAt_id (0:ℝ)).mul_const A).mul (hm'.comp 0 hhalf))).add
    (((hasDerivAt_id (0:ℝ)).mul_const B).mul (hq'.comp 0 hhalf))
  have he : oldTrialOverlap A B=(fun t => weighted haar second second (t/2)+
      (t*A)*weighted haar second meanChannel (t/2)+(t*B)*weighted haar second SU2SevenLinkTransfer.residual (t/2)) :=
    funext (oldTrialOverlap_formula A B)
  rw [he]
  convert h using 1 <;> norm_num [Function.comp_def,id_eq,weighted_zero,haar_meanChannel_mean,haar_residual_mean]
  funext t
  rfl

theorem oldTrial_not_centered_near_zero (A B ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ 0 < oldTrialOverlap A B t := by
  have h := positive_derivative_arbitrarily_small_increase (oldTrialOverlap A B) (1/8)
    (oldTrialOverlap_derivative A B) (by norm_num) ε hε
  simpa only [oldTrialOverlap_zero] using h

/-- The old trial interpreted as a stationary observable via the ACTUAL
homogeneous reset ground function. -/
def oldObservable (A B t : ℝ) (s : State) : ℝ :=
  SU2SevenLinkVariational.unweight t (oddPolynomial t A B) s/weight t s

theorem oldObservable_measurable (A B t : ℝ) : Measurable (oldObservable A B t) :=
  (SU2SevenLinkVariational.unweight_measurable t _ (oddPolynomial_measurable t A B)).div
    ((measurable_const.mul potential_measurable).exp)

private theorem oldObservable_exp (A B t : ℝ) (s : State) :
    oldObservable A B t s=Real.exp (-t*first s/2-t*potential s)*oddPolynomial t A B s := by
  unfold oldObservable SU2SevenLinkVariational.unweight weight
  rw [Real.exp_sub]
  ring

theorem oldObservable_bound (A B t : ℝ) (s : State) :
    |oldObservable A B t s| ≤ Real.exp (3*|t|/2)*(2*∑ i : Fin 3, |(![1,t*A,t*B] : Fin 3 → ℝ) i|) := by
  rw [oldObservable_exp,abs_mul,abs_of_pos (Real.exp_pos _)]
  have hx : |-t*first s| ≤ |t| := by
    rw [abs_mul,abs_neg]
    simpa using mul_le_mul_of_nonneg_left (first_bound s) (abs_nonneg t)
  have hv : |-t*potential s| ≤ |t| := by
    rw [abs_mul,abs_neg]
    simpa using mul_le_mul_of_nonneg_left (potential_bound s) (abs_nonneg t)
  have he : -t*first s/2-t*potential s ≤ 3*|t|/2 := by
    linarith [le_abs_self (-t*first s),le_abs_self (-t*potential s)]
  exact mul_le_mul (Real.exp_le_exp.mpr he) (linear3_bound ![1,t*A,t*B] s) (abs_nonneg _) (Real.exp_pos _).le

theorem oldObservable_memLp (A B t : ℝ) : MemLp (oldObservable A B t) 2 (stationary t) := by
  letI := stationary_probability t
  exact MemLp.of_bound (oldObservable_measurable A B t).aestronglyMeasurable _ (ae_of_all _ (oldObservable_bound A B t))

theorem oldObservable_mean (A B t : ℝ) :
    (∫ s, oldObservable A B t s ∂stationary t)=oldTrialOverlap A B t/partition haar potential (2*t) := by
  rw [stationary,tilted_integral haar potential _ potential_measurable potential_bound]
  unfold expectation weighted oldTrialOverlap
  congr 1
  apply integral_congr_ae
  filter_upwards with s
  have hh : Real.exp ((2*t)*potential s)=weight t s*weight t s := by
    unfold weight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hh,oldObservable]
  field_simp [show weight t s ≠ 0 from Real.exp_ne_zero _]

/-- Direct counterexample to transplanting the one-weight centered trial into
homogeneous spatial weighting. The actual stationary mean is strictly positive,
and its actual L2 domain is already verified, for arbitrarily small positive t. -/
theorem positive_oldObservable_mean_near_zero (A B ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ 0 < ∫ s, oldObservable A B t s ∂stationary t := by
  obtain ⟨t,ht,htε,ho⟩ := oldTrial_not_centered_near_zero A B ε hε
  refine ⟨t,ht,htε,?_⟩
  rw [oldObservable_mean]
  exact div_pos ho (partition_pos haar potential potential_measurable potential_bound _)

/-- Actual Markov realization of the ground-normalized homogeneous reset. -/
def resetKernel (t : ℝ) : ProbabilityTheory.Kernel State State :=
  ProbabilityTheory.Kernel.const State (stationary t)

theorem resetKernel_markov (t : ℝ) : ProbabilityTheory.IsMarkovKernel (resetKernel t) := by
  letI := stationary_probability t
  exact ProbabilityTheory.Kernel.const.instIsMarkovKernel

theorem ground_transform_kernel (t : ℝ) (f : State → ℝ) (s : State) :
    homogeneousStep 0 t (fun r => weight t r*f r) s/
      (partition haar potential (2*t)*weight t s)=∫ r, f r ∂resetKernel t s :=
  ground_transform t f s

/-- Uncentered stationary lag is precisely the square of the mean in this
fully realized model. A positive value is NOT an obstruction to mixing. -/
theorem reset_lag (t : ℝ) (f : State → ℝ) :
    (∫ s, f s*(∫ r, f r ∂resetKernel t s) ∂stationary t)=(∫ s, f s ∂stationary t)^2 := by
  simp only [resetKernel,ProbabilityTheory.Kernel.const_apply]
  rw [integral_mul_const]
  ring

/-- All correctly centered integrable observables have ZERO one-step lag.
This explicitly defeats a false positive from the transplanted uncentered trial. -/
theorem centered_reset_lag_zero (t : ℝ) (f : State → ℝ) (hf : Integrable f (stationary t)) :
    (∫ s, (f s-(∫ r, f r ∂stationary t))*
      (∫ r, f r-(∫ z, f z ∂stationary t) ∂resetKernel t s) ∂stationary t)=0 := by
  letI := stationary_probability t
  have he : (∫ r, f r-(∫ z, f z ∂stationary t) ∂stationary t)=0 := by
    rw [integral_sub hf (integrable_const _)]
    simp
  simp only [resetKernel,ProbabilityTheory.Kernel.const_apply,he,mul_zero,integral_zero]

end OperatorDerivativeRewrite.Foundation.SU2HomogeneousPlaquetteObstruction
