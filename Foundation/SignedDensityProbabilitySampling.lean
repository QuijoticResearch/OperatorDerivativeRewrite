import Foundation.SignedDensityL1Transport

/-! Actual probability sampling of a signed density by normalized total variation. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.SignedDensityProbabilitySampling
open SignedAbsoluteIntegration
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def mass (f : Ω → ℝ) : ℝ := ∫ x, |f x| ∂μ

theorem mass_nonnegative (f : Ω → ℝ) : 0 ≤ mass μ f :=
  integral_nonneg (fun x => abs_nonneg (f x))

theorem mass_ge_integral (f : Ω → ℝ) : |∫ x, f x ∂μ| ≤ mass μ f := by
  simpa only [mass, Real.norm_eq_abs] using norm_integral_le_integral_norm f (μ := μ)

theorem mass_positive_of_integral_one (f : Ω → ℝ) (hf : (∫ x, f x ∂μ)=1) :
    0 < mass μ f := by
  have hh := mass_ge_integral μ f
  rw [hf, abs_one] at hh
  exact lt_of_lt_of_le zero_lt_one hh

def orientation (f : Ω → ℝ) (x : Ω) : ℝ := if 0 ≤ f x then 1 else -1

theorem orientation_measurable (f : Ω → ℝ) (hf : Measurable f) :
    Measurable (orientation f) :=
  Measurable.ite (measurableSet_le measurable_const hf) measurable_const measurable_const

theorem orientation_abs (f : Ω → ℝ) (x : Ω) : |orientation f x|=1 := by
  unfold orientation
  split_ifs <;> norm_num

theorem orientation_density (f : Ω → ℝ) (x : Ω) : |f x| * orientation f x=f x := by
  by_cases h : 0 ≤ f x
  · rw [orientation, if_pos h, abs_of_nonneg h, mul_one]
  · rw [orientation, if_neg h, abs_of_neg (lt_of_not_ge h)]
    ring

def sampler (f : Ω → ℝ) : Measure Ω :=
  (ENNReal.ofReal (mass μ f))⁻¹ • absoluteDensity μ f

def weight (f : Ω → ℝ) (x : Ω) : ℝ := mass μ f * orientation f x

theorem absolute_mass (f : Ω → ℝ) (hf : Integrable f μ) :
    absoluteDensity μ f Set.univ=ENNReal.ofReal (mass μ f) := by
  rw [absoluteDensity, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hf.abs (Eventually.of_forall (fun x => abs_nonneg (f x)))).symm

theorem mass_eq_variation (f : Ω → ℝ) (hf : Integrable f μ) :
    mass μ f=((μ.withDensityᵥ f).variation Set.univ).toReal := by
  rw [variation_density μ f hf, absolute_mass μ f hf, ENNReal.toReal_ofReal (mass_nonnegative μ f)]

theorem sampler_probability (f : Ω → ℝ) (hf : Integrable f μ) (hp : 0 < mass μ f) :
    IsProbabilityMeasure (sampler μ f) := by
  constructor
  rw [sampler, Measure.smul_apply, absolute_mass μ f hf, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

theorem sampler_integrable_iff (f : Ω → ℝ) (hp : 0 < mass μ f) (g : Ω → ℂ) :
    Integrable g (sampler μ f) ↔ Integrable g (absoluteDensity μ f) :=
  integrable_inv_smul_measure (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top

theorem weight_abs (f : Ω → ℝ) (hp : 0 < mass μ f) (x : Ω) :
    |weight μ f x|=mass μ f := by
  rw [weight, abs_mul, abs_of_pos hp, orientation_abs, mul_one]

theorem weight_measurable (f : Ω → ℝ) (hf : Measurable f) : Measurable (weight μ f) :=
  measurable_const.mul (orientation_measurable f hf)

theorem weighted_integrable (f : Ω → ℝ) (hfm : Measurable f) (hp : 0 < mass μ f)
    (g : Ω → ℂ) (hg : Integrable g (absoluteDensity μ f)) :
    Integrable (fun x => weight μ f x • g x) (sampler μ f) := by
  apply (sampler_integrable_iff μ f hp _).mpr
  apply Integrable.mono' (hg.norm.const_mul (mass μ f))
    ((weight_measurable μ f hfm).aestronglyMeasurable.smul hg.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖weight μ f x • g x‖ ≤ mass μ f * ‖g x‖
    rw [norm_smul, Real.norm_eq_abs, weight_abs μ f hp]

theorem integral_orientation {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (f : Ω → ℝ) (hfm : Measurable f) (g : Ω → V) :
    (∫ x, orientation f x • g x ∂absoluteDensity μ f)=∫ x, f x • g x ∂μ := by
  have hmabs : Measurable (fun x => |f x|) := by
    simpa only [Real.norm_eq_abs] using hfm.norm
  rw [absoluteDensity, integral_withDensity_eq_integral_toReal_smul hmabs.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    change (ENNReal.ofReal |f x|).toReal • (orientation f x • g x)=f x • g x
    rw [ENNReal.toReal_ofReal (abs_nonneg _), smul_smul, orientation_density]

theorem signed_integral_sampling (f : Ω → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (hp : 0 < mass μ f) (g : Ω → ℂ) (hg : Integrable g (absoluteDensity μ f)) :
    (∫ᵛ x, g x ∂<•μ.withDensityᵥ f)=∫ x, weight μ f x • g x ∂sampler μ f := by
  rw [integral_density μ f hf hfm g hg, sampler, integral_smul_measure]
  have he : (fun x => weight μ f x • g x) = fun x => mass μ f • (orientation f x • g x) := by
    funext x
    rw [weight, mul_smul]
  rw [he, integral_smul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le,
    smul_smul, inv_mul_cancel₀ (ne_of_gt hp), one_smul, integral_orientation μ f hfm g]

theorem weight_integrable (f : Ω → ℝ) (hf : Integrable f μ) (hfm : Measurable f)
    (hp : 0 < mass μ f) : Integrable (weight μ f) (sampler μ f) := by
  letI := sampler_probability μ f hf hp
  apply Integrable.of_bound (weight_measurable μ f hfm).aestronglyMeasurable (mass μ f)
  exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs, weight_abs μ f hp]

theorem weight_mean (f : Ω → ℝ) (hfm : Measurable f) (hp : 0 < mass μ f) :
    (∫ x, weight μ f x ∂sampler μ f)=∫ x, f x ∂μ := by
  rw [sampler, integral_smul_measure]
  simp only [weight]
  rw [integral_const_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hp), one_mul]
  simpa only [smul_eq_mul, mul_one] using integral_orientation μ f hfm (fun _ => (1:ℝ))

theorem weight_l1 (f : Ω → ℝ) (hf : Integrable f μ) (hp : 0 < mass μ f) :
    (∫ x, |weight μ f x| ∂sampler μ f)=mass μ f := by
  letI := sampler_probability μ f hf hp
  simp only [weight_abs μ f hp, integral_const, probReal_univ, one_smul]

theorem weight_l2_square (f : Ω → ℝ) (hf : Integrable f μ) (hp : 0 < mass μ f) :
    (∫ x, (weight μ f x)^2 ∂sampler μ f)=(mass μ f)^2 := by
  letI := sampler_probability μ f hf hp
  have he : (fun x => (weight μ f x)^2)=fun _ => (mass μ f)^2 := by
    funext x
    rw [← sq_abs (weight μ f x), weight_abs μ f hp]
  rw [he, integral_const, probReal_univ, one_smul]

end OperatorDerivativeRewrite.Foundation.SignedDensityProbabilitySampling
