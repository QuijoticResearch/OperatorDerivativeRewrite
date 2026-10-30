import Foundation.PeriodicLowActionBlock
import Mathlib.Probability.Moments.Variance

/-! Actual positive ground normalization estimates for the homogeneous Wilson slab.
No replacement of its stationary probability by a spatial Gibbs law is made. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.PeriodicGroundMass
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicLowActionBlock

attribute [local irreducible] PeriodicWilsonSlab.kernel boundaryHaar

variable {beta : ℝ} (d : GroundData beta)

private theorem function_integrable : Integrable d.function boundaryHaar := by
  apply Integrable.of_bound d.measurable.aestronglyMeasurable d.upper
  filter_upwards with U
  exact (d.bounds U).2

private theorem weighted_integrable (U : State) :
    Integrable (fun V => kernel beta U V*d.function V) boundaryHaar := by
  convert (d.density_integrable U).mul_const (d.value*d.function U) using 1
  funext V
  unfold GroundData.density
  exact (div_mul_cancel₀ _ (mul_pos d.value_pos (d.function_pos U)).ne').symm

/-- A localized positive block bounds the actual constructed eigenvalue below. -/
theorem eigenvalue_block_lower (B : Set State) (hB : MeasurableSet B)
    (hp : 0 < boundaryHaar.real B) (k : ℝ)
    (hK : ∀ U ∈ B, ∀ V ∈ B, k ≤ kernel beta U V) :
    k*boundaryHaar.real B ≤ d.value := by
  let m : ℝ := ∫ U in B,d.function U ∂boundaryHaar
  have hm : 0 < m := by
    have h := setIntegral_mono_on (integrable_const d.lower).integrableOn
      (function_integrable d).integrableOn hB (fun U _ => (d.bounds U).1)
    have hp' : 0 < boundaryHaar.real B*d.lower := mul_pos hp d.lower_pos
    simp only [setIntegral_const,smul_eq_mul] at h
    exact hp'.trans_le h
  have hrow (U : State) (hU : U ∈ B) : k*m ≤ d.value*d.function U := by
    have h1 := setIntegral_mono_on ((function_integrable d).const_mul k).integrableOn
      ((weighted_integrable d U)).integrableOn hB (fun V hV =>
        mul_le_mul_of_nonneg_right (hK U hU V hV) (d.function_pos V).le)
    rw [integral_const_mul] at h1
    have h2 := setIntegral_le_integral (s := B) ((weighted_integrable d U))
      (ae_of_all _ (fun V => mul_nonneg (kernel_positive beta U V).le (d.function_pos V).le))
    rw [d.eigen U] at h2
    exact h1.trans h2
  have h := setIntegral_mono_on (integrable_const (k*m)).integrableOn
    ((function_integrable d).const_mul d.value).integrableOn hB hrow
  simp only [setIntegral_const,smul_eq_mul,integral_const_mul] at h
  apply (mul_le_mul_iff_left₀ hm).mp
  convert h using 1 <;> ring

/-- For every fixed action budget the native eigenvalue has a genuine lower bound,
with a positive beta-independent constant. This is not a polynomial estimate. -/
theorem eigenvalue_small_rate (eta : ℝ) (he : 0 < eta) :
    ∃ c : ℝ, 0 < c ∧ ∀ beta : ℝ, 0 ≤ beta → ∀ d : GroundData beta,
      c*Real.exp (-beta*eta) ≤ d.value := by
  obtain ⟨B,k,hB,hp,hk,hK⟩ := positive_block eta he
  refine ⟨k*boundaryHaar.real B,mul_pos hk hp,?_⟩
  intro beta hb g
  have h := eigenvalue_block_lower g B hB hp (k*Real.exp (-beta*eta)) (hK beta hb)
  convert h using 1 <;> ring

private theorem mass_square_le : (∫ U,d.function U ∂boundaryHaar)^2 ≤ d.normalizer := by
  have hmem : MemLp d.function 2 boundaryHaar :=
    MemLp.of_bound d.measurable.aestronglyMeasurable d.upper
      (ae_of_all _ (fun U => (d.bounds U).2))
  have h := variance_nonneg d.function boundaryHaar
  rw [variance_eq_sub hmem] at h
  change 0 ≤ d.normalizer-(∫ U,d.function U ∂boundaryHaar)^2 at h
  linarith

/-- Actual eigenfunction decay from the homogeneous spatial half weight. -/
theorem function_spatial_decay (hb : 0 ≤ beta) (U : State) :
    d.value*d.function U ≤ Real.exp (-beta*spatialAction U/2)*
      (∫ V,d.function V ∂boundaryHaar) := by
  have h := integral_mono ((weighted_integrable d U))
    ((function_integrable d).const_mul (Real.exp (-beta*spatialAction U/2)))
    (fun V => mul_le_mul_of_nonneg_right (kernel_spatial_upper beta hb U V) (d.function_pos V).le)
  rw [d.eigen U,integral_const_mul] at h
  exact h


/-- Tail bound for the ACTUAL stationary psi-squared law, not a spatial Gibbs law. -/
theorem action_tail_eigenfactor (hb : 0 ≤ beta) (eps : ℝ) :
    d.stationary.real {U | eps ≤ spatialAction U} ≤ Real.exp (-beta*eps)/d.value^2 := by
  let S : Set State := {U | eps ≤ spatialAction U}
  have hS : MeasurableSet S := measurableSet_le measurable_const spatial_action_measurable
  let C : ℝ := (Real.exp (-beta*eps)/d.value^2)*d.normalizer
  have hC : 0 ≤ C := mul_nonneg
    (div_nonneg (Real.exp_pos _).le (sq_nonneg _)) d.normalizer_pos.le
  have hpoint (U : State) (hU : U ∈ S) : d.function U^2 ≤ C := by
    have h := pow_le_pow_left₀ (mul_pos d.value_pos (d.function_pos U)).le
      (function_spatial_decay d hb U) 2
    have he : Real.exp (-beta*spatialAction U/2)^2=Real.exp (-beta*spatialAction U) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    simp only [mul_pow,he] at h
    have ha : Real.exp (-beta*spatialAction U) ≤ Real.exp (-beta*eps) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hU hb])
    have h1 := h.trans (mul_le_mul_of_nonneg_right ha
      (sq_nonneg (∫ V,d.function V ∂boundaryHaar)))
    have h2 := mul_le_mul_of_nonneg_left (mass_square_le d) (Real.exp_pos (-beta*eps)).le
    have h3 : d.function U^2*d.value^2 ≤ Real.exp (-beta*eps)*d.normalizer := by
      convert h1.trans h2 using 1 <;> ring
    have h4 := (le_div_iff₀ (sq_pos_of_pos d.value_pos)).mpr h3
    convert h4 using 1 <;> dsimp [C] <;> ring
  have h1 := setIntegral_mono_on d.square_integrable.integrableOn
    (integrable_const C).integrableOn hS hpoint
  have h2 : (∫ _U in S,C ∂boundaryHaar) ≤ C := by
    simpa only [integral_const,probReal_univ,one_smul] using
      setIntegral_le_integral (μ := boundaryHaar) (s := S) (integrable_const C) (ae_of_all _ (fun _ => hC))
  have h3 := h1.trans h2
  have hp := d.stationary_integral (S.indicator (fun _ => 1))
  have hpi : (∫ U,S.indicator (fun _ => (1:ℝ)) U ∂d.stationary)=d.stationary.real S :=
    integral_indicator_one hS
  rw [hpi] at hp
  have hi : (fun U => d.function U^2*S.indicator (fun _ => (1:ℝ)) U)=
      S.indicator (fun U => d.function U^2) := by
    funext U
    by_cases hU : U ∈ S <;> simp [hU]
  rw [hi,integral_indicator hS] at hp
  change d.stationary.real S ≤ _
  rw [hp]
  calc
    _ ≤ C/d.normalizer := div_le_div_of_nonneg_right h3 d.normalizer_pos.le
    _ = _ := by
      dsimp [C]
      exact mul_div_cancel_right₀ _ d.normalizer_pos.ne'

/-- Fixed-threshold exponential concentration for every actual positive ground.
The constant depends on the threshold and this finite cell. -/
theorem action_tail_exponential (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ beta : ℝ, 0 ≤ beta → ∀ g : GroundData beta,
      g.stationary.real {U | eps ≤ spatialAction U} ≤ C*Real.exp (-beta*eps/2) := by
  obtain ⟨c,hc,hl⟩ := eigenvalue_small_rate (eps/4) (by positivity)
  refine ⟨1/c^2,div_pos zero_lt_one (sq_pos_of_pos hc),?_⟩
  intro beta hb g
  have hv := hl beta hb g
  have hsq := pow_le_pow_left₀ (mul_pos hc (Real.exp_pos _)).le hv 2
  have hdiv := div_le_div_of_nonneg_left (Real.exp_pos (-beta*eps)).le
    (sq_pos_of_pos (mul_pos hc (Real.exp_pos (-beta*(eps/4))))) hsq
  have he : Real.exp (-beta*eps)=Real.exp (-beta*eps/2)*Real.exp (-beta*(eps/4))^2 := by
    rw [pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  have heq : Real.exp (-beta*eps)/(c*Real.exp (-beta*(eps/4)))^2=
      (1/c^2)*Real.exp (-beta*eps/2) := by
    rw [he]
    field_simp [hc.ne',(Real.exp_pos (-beta*(eps/4))).ne']
    <;> ring
  exact (action_tail_eigenfactor g hb eps).trans (hdiv.trans_eq heq)

/-- Genuine concentration of the constructed native stationary laws at increasing coupling. -/
theorem action_tail_tendsto_zero (eps : ℝ) (heps : 0 < eps) :
    Filter.Tendsto (fun beta : ℝ => (ground beta).stationary.real {U | eps ≤ spatialAction U})
      Filter.atTop (nhds 0) := by
  obtain ⟨C,hC,hb⟩ := action_tail_exponential eps heps
  have ht : Filter.Tendsto (fun beta : ℝ => C*Real.exp ((-eps/2)*beta))
      Filter.atTop (nhds 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (Filter.tendsto_id.const_mul_atTop_of_neg (by linarith : -eps/2 < 0))).const_mul C
  have ht' : Filter.Tendsto (fun beta : ℝ => C*Real.exp (-beta*eps/2))
      Filter.atTop (nhds 0) := by
    convert ht using 1
    funext beta
    congr 2 <;> ring
  apply squeeze_zero' (Filter.Eventually.of_forall (fun beta => measureReal_nonneg)) ?_ ht'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with beta hbeta
  exact hb beta hbeta (ground beta)

end OperatorDerivativeRewrite.Foundation.PeriodicGroundMass
