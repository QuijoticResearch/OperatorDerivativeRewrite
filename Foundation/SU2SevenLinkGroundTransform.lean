import Foundation.SU2SevenLinkParity
import Foundation.YMPositiveKernel
import Mathlib.Probability.Kernel.WithDensity

/-! A genuine conditional ground-state Markov realization for the actual
seven-link spatial transfer. GroundData is an explicit missing-input contract,
NOT an existence axiom. All probabilities and integral identities are constructed. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkGroundTransform
open SU2SevenLinkTransfer SU2SevenLinkVariational SU2SevenLinkOddTrial
open SU2SevenLinkSpatialSeparation SU2SevenLinkParity

/-- No inhabitant is postulated. The actual eigenfunction equation and global
bounds are the precise unresolved ground-state inputs. Center parity is separate. -/
structure GroundData (β t : ℝ) where
  value : ℝ
  function : State → ℝ
  lower : ℝ
  upper : ℝ
  value_pos : 0 < value
  lower_pos : 0 < lower
  measurable : Measurable function
  bounds : ∀ s, lower ≤ function s ∧ |function s| ≤ upper
  eigen : ∀ s, spatialStep β t function s=value*function s

namespace GroundData
variable {β t : ℝ} (g : GroundData β t)

theorem function_pos (s : State) : 0 < g.function s := g.lower_pos.trans_le (g.bounds s).1

theorem square_integrable : Integrable (fun s => g.function s^2) haar := by
  apply Integrable.of_bound (g.measurable.pow_const 2).aestronglyMeasurable (g.upper^2)
  filter_upwards with s
  rw [Real.norm_eq_abs,abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (g.bounds s).2 2

def normalizer : ℝ := ∫ s, g.function s^2 ∂haar

theorem normalizer_pos : 0 < g.normalizer := by
  have h := integral_mono (integrable_const (g.lower^2)) g.square_integrable
    (fun s => pow_le_pow_left₀ g.lower_pos.le (g.bounds s).1 2)
  simp only [integral_const,probReal_univ,one_smul] at h
  exact lt_of_lt_of_le (sq_pos_of_pos g.lower_pos) h

private theorem square_mass : SignedDensityProbabilitySampling.mass haar (fun s => g.function s^2)=g.normalizer := by
  unfold SignedDensityProbabilitySampling.mass normalizer
  apply integral_congr_ae
  filter_upwards with s
  exact abs_of_nonneg (sq_nonneg (g.function s))

/-- Actual probability with density psi^2/Z against the seven-link Haar law. -/
def stationary : Measure State := SignedDensityProbabilitySampling.sampler haar (fun s => g.function s^2)

theorem stationary_probability : IsProbabilityMeasure g.stationary :=
  SignedDensityProbabilitySampling.sampler_probability haar _ g.square_integrable (by rw [g.square_mass]; exact g.normalizer_pos)

theorem stationary_integral (f : State → ℝ) :
    (∫ s, f s ∂g.stationary)=(∫ s, g.function s^2*f s ∂haar)/g.normalizer := by
  have h := YMPositiveKernel.positive_sampler_integral haar (fun s => g.function s^2) f
    (g.measurable.pow_const 2) (fun s => sq_nonneg _) (by rw [g.square_mass]; exact g.normalizer_pos)
  rw [g.square_mass] at h
  exact h

/-- Density relative to the actual seven-link Wilson transition, not a
row-normalized spatial kernel. The eigenvalue is explicitly in the denominator. -/
def density (s r : State) : ℝ :=
  halfWeight t s*halfWeight t r*g.function r/(g.value*g.function s)

theorem density_nonneg (s r : State) : 0 ≤ g.density s r := by
  unfold density halfWeight
  exact (div_pos (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (g.function_pos r))
    (mul_pos g.value_pos (g.function_pos s))).le

theorem density_measurable : Measurable (Function.uncurry g.density) := by
  unfold density Function.uncurry
  exact (((halfWeight_measurable t).comp measurable_fst).mul
    ((halfWeight_measurable t).comp measurable_snd)).mul
    (g.measurable.comp measurable_snd) |>.div (measurable_const.mul (g.measurable.comp measurable_fst))

private theorem weighted_function_integrable (s : State) :
    Integrable (fun r => halfWeight t r*g.function r) (transition β s) := by
  letI := transition_markov β
  apply Integrable.of_bound ((halfWeight_measurable t).mul g.measurable).aestronglyMeasurable
    (Real.exp (|t|/2)*|g.upper|)
  filter_upwards with r
  change ‖halfWeight t r*g.function r‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul (halfWeight_bound t r) ((g.bounds r).2.trans (le_abs_self _)) (abs_nonneg _) (Real.exp_pos _).le

theorem density_integrable (s : State) : Integrable (g.density s) (transition β s) := by
  convert ((g.weighted_function_integrable s).const_mul (halfWeight t s)).div_const (g.value*g.function s) using 1
  funext r
  unfold density
  ring

theorem density_integral (s : State) : (∫ r, g.density s r ∂transition β s)=1 := by
  unfold density
  simp_rw [mul_assoc]
  rw [integral_div,integral_const_mul,transition_integral β (fun r => halfWeight t r*g.function r)
    ((halfWeight_measurable t).mul g.measurable)]
  change spatialStep β t g.function s/(g.value*g.function s)=1
  rw [g.eigen,div_self (mul_pos g.value_pos (g.function_pos s)).ne']

/-- Actual measurable ground-transform transition kernel. -/
def kernel : Kernel State State := by
  letI := transition_markov β
  exact (transition β).withDensity (fun s r => ENNReal.ofReal (g.density s r))

theorem kernel_apply (s : State) :
    g.kernel s=(transition β s).withDensity (fun r => ENNReal.ofReal (g.density s r)) := by
  letI := transition_markov β
  exact Kernel.withDensity_apply _ g.density_measurable.ennreal_ofReal s

theorem kernel_markov : IsMarkovKernel g.kernel := by
  constructor
  intro s
  constructor
  rw [g.kernel_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (g.density_integrable s) (ae_of_all _ (g.density_nonneg s)),g.density_integral]
  norm_num

/-- Actual kernel integration agrees with the literal spatial ground transform. -/
theorem kernel_integral (f : State → ℝ) (hf : Measurable f) (s : State) :
    (∫ r, f r ∂g.kernel s)=spatialStep β t (fun r => g.function r*f r) s/(g.value*g.function s) := by
  rw [g.kernel_apply,integral_withDensity_eq_integral_toReal_smul
    ((Measurable.of_uncurry_left g.density_measurable).ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (g.density_nonneg s _),smul_eq_mul]
  have he (r : State) : g.density s r*f r=
      (halfWeight t s*(halfWeight t r*(g.function r*f r)))/(g.value*g.function s) := by unfold density; ring
  simp_rw [he]
  rw [integral_div,integral_const_mul,transition_integral β (fun r => halfWeight t r*(g.function r*f r)) ((halfWeight_measurable t).mul (g.measurable.mul hf))]
  rfl

/-- Exact stationary pairing under the constructed probability/kernel. This
identity has no postulated stationary distribution or spectral interpretation. -/
theorem stationary_pairing (f k : State → ℝ) (hk : Measurable k) :
    (∫ s, f s*(∫ r, k r ∂g.kernel s) ∂g.stationary)=
      spatialPairing β t (fun s => g.function s*f s) (fun s => g.function s*k s)/(g.value*g.normalizer) := by
  rw [g.stationary_integral]
  simp_rw [g.kernel_integral k hk]
  have he (s : State) : g.function s^2*(f s*(spatialStep β t (fun r => g.function r*k r) s/(g.value*g.function s)))=
      ((g.function s*f s)*spatialStep β t (fun r => g.function r*k r) s)/g.value := by
    field_simp [(g.function_pos s).ne',g.value_pos.ne']
    <;> ring
  simp_rw [he]
  rw [integral_div,← spatialPairing_integral]
  ring

private theorem spatial_symmetric (f k : State → ℝ) (hf : Measurable f) (hk : Measurable k)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |k s| ≤ C) :
    spatialPairing β t f k=spatialPairing β t k f := by
  unfold spatialPairing
  apply pairing_symmetric β _ _ ((halfWeight_measurable t).mul hf) ((halfWeight_measurable t).mul hk)
    (Real.exp (|t|/2)*|B|) (Real.exp (|t|/2)*|C|)
  · intro s
    change |halfWeight t s*f s| ≤ _
    rw [abs_mul]
    exact mul_le_mul (halfWeight_bound t s) ((hb s).trans (le_abs_self _)) (abs_nonneg _) (Real.exp_pos _).le
  · intro s
    change |halfWeight t s*k s| ≤ _
    rw [abs_mul]
    exact mul_le_mul (halfWeight_bound t s) ((hc s).trans (le_abs_self _)) (abs_nonneg _) (Real.exp_pos _).le

/-- Stationarity for EVERY bounded measurable probe of the actual Markov kernel. -/
theorem kernel_stationary (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ s, |f s| ≤ B) :
    (∫ s, ∫ r, f r ∂g.kernel s ∂g.stationary)=∫ s, f s ∂g.stationary := by
  have hp := g.stationary_pairing (fun _ => 1) f hf
  simp only [mul_one,one_mul] at hp
  rw [hp]
  have hbψf (s : State) : |g.function s*f s| ≤ |g.upper| * |B| := by
    rw [abs_mul]
    exact mul_le_mul ((g.bounds s).2.trans (le_abs_self _)) ((hb s).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
  rw [spatial_symmetric g.function (fun s => g.function s*f s) g.measurable (g.measurable.mul hf)
    g.upper _ (fun s => (g.bounds s).2) hbψf,spatialPairing_integral]
  simp_rw [g.eigen]
  have he (s : State) : (g.function s*f s)*(g.value*g.function s)=g.value*(g.function s^2*f s) := by ring
  simp_rw [he]
  rw [integral_const_mul,g.stationary_integral]
  field_simp [g.value_pos.ne',g.normalizer_pos.ne']

/-- Exact reversible pairings, now for the actual stationary Markov law. -/
theorem stationary_reversible (f k : State → ℝ) (hf : Measurable f) (hk : Measurable k)
    (B C : ℝ) (hb : ∀ s, |f s| ≤ B) (hc : ∀ s, |k s| ≤ C) :
    (∫ s, f s*(∫ r, k r ∂g.kernel s) ∂g.stationary)=
      ∫ s, k s*(∫ r, f r ∂g.kernel s) ∂g.stationary := by
  rw [g.stationary_pairing f k hk,g.stationary_pairing k f hf]
  congr 1
  apply spatial_symmetric _ _ (g.measurable.mul hf) (g.measurable.mul hk)
    (|g.upper| * |B|) (|g.upper| * |C|)
  · intro s
    change |g.function s*f s| ≤ _
    rw [abs_mul]
    exact mul_le_mul ((g.bounds s).2.trans (le_abs_self _)) ((hb s).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
  · intro s
    change |g.function s*k s| ≤ _
    rw [abs_mul]
    exact mul_le_mul ((g.bounds s).2.trans (le_abs_self _)) ((hc s).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

/-- Literal inverse ground transform of the verified spatial trial. -/
def observable (A B : ℝ) (s : State) : ℝ := unweight t (oddPolynomial t A B) s/g.function s

theorem observable_measurable (A B : ℝ) : Measurable (g.observable A B) :=
  (unweight_measurable t _ (oddPolynomial_measurable t A B)).div g.measurable

theorem observable_centered (A B : ℝ) (heven : ∀ s, g.function (flip s)=g.function s) :
    (∫ s, g.observable A B s ∂g.stationary)=0 := by
  rw [g.stationary_integral]
  have he (s : State) : g.function s^2*g.observable A B s=unweight t (oddPolynomial t A B) s*g.function s := by
    unfold observable
    field_simp [(g.function_pos s).ne']
    <;> ring
  simp_rw [he]
  rw [trial_orthogonal t A B g.function heven,zero_div]

theorem observable_square (A B : ℝ) :
    (∫ s, (g.observable A B s)^2 ∂g.stationary)=denominator t A B/g.normalizer := by
  rw [g.stationary_integral]
  have he (s : State) : g.function s^2*(g.observable A B s)^2=(unweight t (oddPolynomial t A B) s)^2 := by
    unfold observable
    field_simp [(g.function_pos s).ne']
  simp_rw [he]
  rw [unweighted_trial_norm]

theorem observable_square_pos (A B : ℝ) : 0 < ∫ s, (g.observable A B s)^2 ∂g.stationary := by
  rw [g.observable_square]
  exact div_pos (denominator_positive t A B) g.normalizer_pos

theorem observable_lag (A B : ℝ) :
    (∫ s, g.observable A B s*(∫ r, g.observable A B r ∂g.kernel s) ∂g.stationary)=
      spatialPairing β t (unweight t (oddPolynomial t A B)) (unweight t (oddPolynomial t A B))/(g.value*g.normalizer) := by
  rw [g.stationary_pairing _ _ (g.observable_measurable A B)]
  have he (s : State) : g.function s*g.observable A B s=unweight t (oddPolynomial t A B) s := by
    unfold observable
    field_simp [(g.function_pos s).ne']
  simp_rw [he]

theorem observable_bound (A B : ℝ) (s : State) :
    |g.observable A B s| ≤ Real.exp (|t|/2)*(2*∑ i : Fin 3, |(![1,t*A,t*B] : Fin 3 → ℝ) i|)/g.lower := by
  let M := Real.exp (|t|/2)*(2*∑ i : Fin 3, |(![1,t*A,t*B] : Fin 3 → ℝ) i|)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hb : |unweight t (oddPolynomial t A B) s| ≤ M := by
    change |halfWeight (-t) s*oddPolynomial t A B s| ≤ M
    rw [abs_mul]
    have he := halfWeight_bound (-t) s
    rw [abs_neg] at he
    exact mul_le_mul he (linear3_bound ![1,t*A,t*B] s) (abs_nonneg _) (Real.exp_pos _).le
  unfold observable
  rw [abs_div,abs_of_pos (g.function_pos s)]
  apply (div_le_div_iff₀ (g.function_pos s) g.lower_pos).mpr
  exact (mul_le_mul_of_nonneg_right hb g.lower_pos.le).trans (mul_le_mul_of_nonneg_left (g.bounds s).1 hM)

theorem observable_memLp (A B : ℝ) : MemLp (g.observable A B) 2 g.stationary := by
  letI := g.stationary_probability
  exact MemLp.of_bound (g.observable_measurable A B).aestronglyMeasurable _ (ae_of_all _ (g.observable_bound A B))

/-- The supplied eigenvalue is bounded by the VERIFIED certificate. This
consequence is proved, not added to GroundData as a hidden spectral premise. -/
theorem value_le_certificate (ht : |t| ≤ 1)
    (hsmall : |SU2WilsonGroundCertificate.linearCoefficient (SU2WilsonConvolution.coefficient β^4)| * |t|+
      |SU2WilsonGroundCertificate.quadraticTrialCoefficient (SU2WilsonConvolution.coefficient β^4)
        (SU2QuadraticWilsonChannel.quadraticCoefficient β^4)| * |t|^2 ≤ 1/2) :
    g.value ≤ 1+SU2WilsonGroundCertificate.vacuumSecond (SU2WilsonConvolution.coefficient β^4)*t^2+
      2*SU2WilsonGroundCertificate.eigenErrorConstant (SU2WilsonConvolution.coefficient β^4)
        (SU2QuadraticWilsonChannel.quadraticCoefficient β^4)*|t|^3 := by
  let u := trialVacuum β t
  let r := fun s => g.function s/u s
  let l := Real.exp (-|t|/2)/2
  have hl : 0 < l := div_pos (Real.exp_pos _) (by norm_num)
  have hr : Measurable r := g.measurable.div (trialVacuum_measurable β t)
  have hb (s : State) : |r s| ≤ |g.upper|/l := by
    have hup : 0 < u s := trialVacuum_positive β t hsmall s
    dsimp [r]
    rw [abs_div,abs_of_pos hup]
    apply (div_le_div_iff₀ hup hl).mpr
    exact (mul_le_mul_of_nonneg_right ((g.bounds s).2.trans (le_abs_self _)) hl.le).trans
      (mul_le_mul_of_nonneg_left (trialVacuum_lower β t hsmall s) (abs_nonneg _))
  have h := trialVacuum_form_bound β t ht hsmall r hr (|g.upper|/l) hb
  have he (s : State) : trialVacuum β t s*r s=g.function s := by
    dsimp [r,u]
    field_simp [(trialVacuum_positive β t hsmall s).ne']
  simp_rw [he] at h
  rw [spatialPairing_integral] at h
  simp_rw [g.eigen] at h
  have hid (s : State) : g.function s*(g.value*g.function s)=g.value*g.function s^2 := by ring
  simp_rw [hid] at h
  rw [integral_const_mul] at h
  exact (mul_le_mul_iff_left₀ g.normalizer_pos).mp h

/-- Exact nonzero stationary Rayleigh ratio, with ACTUAL probability integrals. -/
theorem observable_lag_ratio (A B : ℝ) :
    (∫ s, g.observable A B s*(∫ r, g.observable A B r ∂g.kernel s) ∂g.stationary)/
      (∫ s, (g.observable A B s)^2 ∂g.stationary)=trialQuotient β t A B/g.value := by
  rw [g.observable_lag,g.observable_square]
  unfold trialQuotient
  field_simp [g.normalizer_pos.ne',g.value_pos.ne',(denominator_positive t A B).ne']

/-- Conditional genuine stationary obstruction. The Markov law, centering,
positive variance and lag identity are all constructed; existence of GroundData
at nonzero tilt is STILL an explicit unresolved premise. -/
theorem stationary_lag_obstruction
    (heven : ∀ s, g.function (flip s)=g.function s)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hsmall : |SU2WilsonGroundCertificate.linearCoefficient (SU2WilsonConvolution.coefficient β^4)| * |t|+
      |SU2WilsonGroundCertificate.quadraticTrialCoefficient (SU2WilsonConvolution.coefficient β^4)
        (SU2QuadraticWilsonChannel.quadraticCoefficient β^4)| * |t|^2 ≤ 1/2)
    (herror : SU2WilsonConvolution.coefficient β^4*
      comparisonError (normSecond (oddA β) (oddB β)) (normError (oddA β) (oddB β))
        (SU2WilsonGroundCertificate.vacuumSecond (SU2WilsonConvolution.coefficient β^4))
        (SU2WilsonGroundCertificate.eigenErrorConstant (SU2WilsonConvolution.coefficient β^4)
          (SU2QuadraticWilsonChannel.quadraticCoefficient β^4))*t < leadingGap β) :
    (∫ s, g.observable (oddA β) (oddB β) s ∂g.stationary)=0 ∧
    0 < (∫ s, (g.observable (oddA β) (oddB β) s)^2 ∂g.stationary) ∧
    SU2WilsonConvolution.coefficient β^4 <
      (∫ s, g.observable (oddA β) (oddB β) s*(∫ r, g.observable (oddA β) (oddB β) r ∂g.kernel s) ∂g.stationary)/
        (∫ s, (g.observable (oddA β) (oddB β) s)^2 ∂g.stationary) := by
  refine ⟨g.observable_centered _ _ heven,g.observable_square_pos _ _,?_⟩
  rw [g.observable_lag_ratio]
  apply normalized_trial_separation β t g.value g.value_pos ht ht1 _ herror
  simpa only [abs_of_pos ht] using g.value_le_certificate (by rwa [abs_of_pos ht]) hsmall

private theorem average_eigen (s : State) :
    spatialStep β t (fun r => (g.function r+g.function (flip r))/2) s=
      g.value*((g.function s+g.function (flip s))/2) := by
  let f := fun r => halfWeight t r*g.function r
  let k := fun r => halfWeight t r*g.function (flip r)
  have hf : Measurable f := (halfWeight_measurable t).mul g.measurable
  have hk : Measurable k := (halfWeight_measurable t).mul (g.measurable.comp flip_measurable)
  have hb (r : State) : |f r| ≤ Real.exp (|t|/2)*|g.upper| := by
    dsimp [f]
    rw [abs_mul]
    exact mul_le_mul (halfWeight_bound t r) ((g.bounds r).2.trans (le_abs_self _)) (abs_nonneg _) (Real.exp_pos _).le
  have hc (r : State) : |k r| ≤ Real.exp (|t|/2)*|g.upper| := by
    dsimp [k]
    rw [abs_mul]
    exact mul_le_mul (halfWeight_bound t r) ((g.bounds (flip r)).2.trans (le_abs_self _)) (abs_nonneg _) (Real.exp_pos _).le
  have hi := step_integrable β f hf _ hb s
  have hj := step_integrable β k hk _ hc s
  have hlin : spatialStep β t (fun r => (g.function r+g.function (flip r))/2) s=
      (spatialStep β t g.function s+spatialStep β t (fun r => g.function (flip r)) s)/2 := by
    unfold spatialStep SU2SevenLinkTransfer.step
    have he (v : State) : Real.exp (t*first (s*v)/2)*((g.function (s*v)+g.function (flip (s*v)))/2)=
        (f (s*v)+k (s*v))/2 := by dsimp [f,k,halfWeight]; ring
    simp_rw [he]
    rw [integral_div,integral_add hi hj]
    dsimp [f,k,halfWeight]
    ring
  rw [hlin,← spatialStep_flip,g.eigen,g.eigen]
  ring

/-- Any supplied positive bounded eigenfunction can be averaged into the even
center sector WITHOUT assuming uniqueness or a Perron theorem. Thus parity
need not be a further existence hypothesis in the final stationary test. -/
def evenized : GroundData β t where
  value := g.value
  function := fun s => (g.function s+g.function (flip s))/2
  lower := g.lower
  upper := g.upper
  value_pos := g.value_pos
  lower_pos := g.lower_pos
  measurable := (g.measurable.add (g.measurable.comp flip_measurable)).div_const 2
  bounds s := by
    constructor
    · linarith [(g.bounds s).1,(g.bounds (flip s)).1]
    · rw [abs_of_pos (by linarith [g.function_pos s,g.function_pos (flip s)] :
        0 < (g.function s+g.function (flip s))/2)]
      have h1 := (le_abs_self (g.function s)).trans (g.bounds s).2
      have h2 := (le_abs_self (g.function (flip s))).trans (g.bounds (flip s)).2
      linarith
  eigen := g.average_eigen

theorem evenized_even (s : State) : g.evenized.function (flip s)=g.evenized.function s := by
  change (g.function (flip s)+g.function (flip (flip s)))/2=(g.function s+g.function (flip s))/2
  rw [SU2SevenLinkParity.flip_flip]
  ring

/-- A genuine nonvacuous instance at zero spatial tilt for EVERY Wilson
parameter. This does not settle existence at the nonzero tilt used in separation. -/
def kinetic (β : ℝ) : GroundData β 0 where
  value := 1
  function := fun _ => 1
  lower := 1
  upper := 1
  value_pos := by norm_num
  lower_pos := by norm_num
  measurable := measurable_const
  bounds _ := by norm_num
  eigen s := by
    letI := noise_probability β
    simp [spatialStep,SU2SevenLinkTransfer.step]

theorem kinetic_kernel (β : ℝ) : (kinetic β).kernel=transition β := by
  ext s
  rw [(kinetic β).kernel_apply]
  simp [density,kinetic,halfWeight]

end GroundData

/-- All stationary-realization and parity obligations in the local comparison
reduce to existence of ONE uniformly positive bounded measurable eigenfunction. No such nonzero-tilt
eigenfunction is postulated. The interval depends only on the actual Wilson law. -/
theorem exists_stationary_obstruction_interval (β : ℝ) (hc : SU2WilsonConvolution.coefficient β ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ g : GroundData β t,
      let v := g.evenized
      let f := v.observable (oddA β) (oddB β)
      (∫ s, f s ∂v.stationary)=0 ∧
      0 < (∫ s, (f s)^2 ∂v.stationary) ∧
      SU2WilsonConvolution.coefficient β^4 <
        (∫ s, f s*(∫ r, f r ∂v.kernel s) ∂v.stationary)/(∫ s, (f s)^2 ∂v.stationary) := by
  obtain ⟨δ,hδ,hδ1,hall⟩ := exists_separation_interval β hc
  refine ⟨δ,hδ,hδ1,?_⟩
  intro t ht htδ g
  dsimp only
  refine ⟨g.evenized.observable_centered _ _ g.evenized_even,g.evenized.observable_square_pos _ _,?_⟩
  obtain ⟨hsmall,hsep⟩ := hall t ht htδ
  have ht1 : |t| ≤ 1 := by rw [abs_of_pos ht]; exact htδ.le.trans hδ1
  have hv := g.evenized.value_le_certificate ht1 hsmall
  rw [abs_of_pos ht] at hv
  rw [g.evenized.observable_lag_ratio]
  apply (lt_div_iff₀ g.evenized.value_pos).mpr
  unfold trialQuotient
  apply (lt_div_iff₀ (denominator_positive t (oddA β) (oddB β))).mpr
  rw [unweighted_trial_norm] at hsep
  have ha : 0 ≤ SU2WilsonConvolution.coefficient β^4 := by positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv ha)
    (denominator_positive t (oddA β) (oddB β)).le).trans_lt hsep

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkGroundTransform
