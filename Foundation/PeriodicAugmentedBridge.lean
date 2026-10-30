import Foundation.PeriodicGroundBridge

/-!
# Actual augmented middle law with both temporal Haar fields

The positive product of two genuine Wilson slab weights defines an ordinary
probability on the middle spatial field and two temporal fields. Its middle
projection is the actual ground-transform bridge, as a measure-preserving
map. The exact phase has the central spatial action once. No one-link
staple conditional, covariance rate or mass-gap theorem is assumed here.
-/

noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicAugmentedBridge
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicGroundBridge
attribute [local irreducible] PeriodicWilsonSlab.kernel weight boundaryHaar gaugeHaar

abbrev Space := State × (Gauge × Gauge)
def reference : Measure Space := boundaryHaar.prod (gaugeHaar.prod gaugeHaar)
instance reference_probability : IsProbabilityMeasure reference := by unfold reference; infer_instance

def density (beta : ℝ) (U W : State) (q : Space) : ℝ :=
  weight beta U q.1 q.2.1*weight beta q.1 W q.2.2

def centralAction (U W : State) (q : Space) : ℝ :=
  spatialAction q.1+temporalAction U q.1 q.2.1+temporalAction q.1 W q.2.2

theorem paired_action (U W : State) (q : Space) :
    halfAction U q.1 q.2.1+halfAction q.1 W q.2.2=
      spatialAction U/2+centralAction U W q+spatialAction W/2 := by
  unfold halfAction centralAction
  ring

theorem density_phase (beta : ℝ) (U W : State) (q : Space) :
    density beta U W q=Real.exp (-beta*(spatialAction U/2+spatialAction W/2))*
      Real.exp (-beta*centralAction U W q) := by
  unfold density weight
  rw [← Real.exp_add]
  have hp := paired_action U W q
  rw [← Real.exp_add]
  congr 1
  calc
    _ = -beta*(halfAction U q.1 q.2.1+halfAction q.1 W q.2.2) := by ring
    _ = -beta*(spatialAction U/2+centralAction U W q+spatialAction W/2) := by rw [hp]
    _ = _ := by ring

theorem density_measurable (beta : ℝ) (U W : State) : Measurable (density beta U W) := by
  have h1 : Measurable (fun q : Space => ((U,q.1),q.2.1)) :=
    (measurable_const.prodMk measurable_fst).prodMk (measurable_fst.comp measurable_snd)
  have h2 : Measurable (fun q : Space => ((q.1,W),q.2.2)) :=
    (measurable_fst.prodMk measurable_const).prodMk (measurable_snd.comp measurable_snd)
  unfold density
  exact ((weight_joint_measurable beta).comp h1).mul ((weight_joint_measurable beta).comp h2)

theorem density_pos (beta : ℝ) (U W : State) (q : Space) : 0<density beta U W q := by
  unfold density weight
  exact mul_pos (Real.exp_pos _) (Real.exp_pos _)

theorem density_upper (beta : ℝ) (U W : State) (q : Space) :
    density beta U W q ≤ Real.exp (768*|beta|)^2 := by
  have hp : 0 ≤ weight beta q.1 W q.2.2 :=
    (Real.exp_pos _).le.trans (weight_bounds beta q.1 W q.2.2).1
  have h := mul_le_mul (weight_bounds beta U q.1 q.2.1).2
    (weight_bounds beta q.1 W q.2.2).2 hp (Real.exp_pos _).le
  simpa only [density,pow_two] using h

theorem density_integrable (beta : ℝ) (U W : State) : Integrable (density beta U W) reference := by
  apply Integrable.of_bound (density_measurable beta U W).aestronglyMeasurable (Real.exp (768*|beta|)^2)
  filter_upwards with q
  rw [Real.norm_eq_abs,abs_of_pos (density_pos beta U W q)]
  exact density_upper beta U W q

theorem gauge_pair_integral (beta : ℝ) (U W V : State) :
    (∫ ab : Gauge × Gauge,density beta U W (V,ab) ∂gaugeHaar.prod gaugeHaar)=bridgeWeight beta U W V := by
  simpa only [density,bridgeWeight,PeriodicWilsonSlab.kernel] using
    (integral_prod_mul (weight beta U V) (weight beta V W) (μ := gaugeHaar) (ν := gaugeHaar))

theorem total_integral (beta : ℝ) (U W : State) :
    (∫ q,density beta U W q ∂reference)=normalizer beta U W := by
  rw [reference,integral_prod _ (density_integrable beta U W)]
  simp_rw [gauge_pair_integral]
  rfl

theorem mass_identity (beta : ℝ) (U W : State) :
    SignedDensityProbabilitySampling.mass reference (density beta U W)=normalizer beta U W := by
  unfold SignedDensityProbabilitySampling.mass
  simp_rw [abs_of_pos (density_pos beta U W _)]
  exact total_integral beta U W

def law (beta : ℝ) (U W : State) : Measure Space :=
  SignedDensityProbabilitySampling.sampler reference (density beta U W)

instance law_probability (beta : ℝ) (U W : State) : IsProbabilityMeasure (law beta U W) :=
  SignedDensityProbabilitySampling.sampler_probability reference _ (density_integrable beta U W)
    (by rw [mass_identity]; exact normalizer_pos beta U W)

theorem integral_formula (beta : ℝ) (U W : State) (f : Space → ℝ) :
    (∫ q,f q ∂law beta U W)=(∫ q,density beta U W q*f q ∂reference)/normalizer beta U W := by
  have h := YMPositiveKernel.positive_sampler_integral reference (density beta U W) f
    (density_measurable beta U W) (fun q => (density_pos beta U W q).le)
    (by rw [mass_identity]; exact normalizer_pos beta U W)
  rw [mass_identity] at h
  exact h

private theorem probe_integrable (beta : ℝ) (U W : State) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ V,|f V| ≤ B) :
    Integrable (fun q : Space => density beta U W q*f q.1) reference := by
  apply Integrable.of_bound ((density_measurable beta U W).mul
    (hf.comp measurable_fst)).aestronglyMeasurable (Real.exp (768*|beta|)^2*|B|)
  filter_upwards with q
  change ‖density beta U W q*f q.1‖ ≤ Real.exp (768*|beta|)^2*|B|
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (density_pos beta U W q)]
  exact mul_le_mul (density_upper beta U W q) ((hb q.1).trans (le_abs_self B))
    (abs_nonneg _) (sq_nonneg _)

theorem projection_integral (beta : ℝ) (U W : State) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ V,|f V| ≤ B) :
    (∫ q,f q.1 ∂law beta U W)=∫ V,f V ∂PeriodicGroundBridge.law beta U W := by
  rw [integral_formula,PeriodicGroundBridge.integral_formula]
  congr 1
  rw [reference,integral_prod _ (probe_integrable beta U W f hf B hb)]
  apply integral_congr_ae
  filter_upwards with V
  rw [integral_mul_const,gauge_pair_integral]

theorem projection_preserving (beta : ℝ) (U W : State) :
    MeasurePreserving Prod.fst (law beta U W) (PeriodicGroundBridge.law beta U W) := by
  refine ⟨measurable_fst,?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_fst hs]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  have hi := projection_integral beta U W (s.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hs) 1 (fun V => by by_cases hV : V ∈ s <;> simp [hV])
  have he : (fun q : Space => s.indicator (fun _ => (1 : ℝ)) q.1)=
      (Prod.fst ⁻¹' s).indicator (fun _ : Space => (1 : ℝ)) := by
    funext q
    by_cases hq : q.1 ∈ s <;> simp [hq]
  rw [he] at hi
  have hL := integral_indicator_one (μ := law beta U W)
    (hs.preimage (measurable_fst : Measurable (Prod.fst : Space → State)))
  have hR := integral_indicator_one (μ := PeriodicGroundBridge.law beta U W) hs
  exact hL.symm.trans (hi.trans hR)

end OperatorDerivativeRewrite.Foundation.PeriodicAugmentedBridge
