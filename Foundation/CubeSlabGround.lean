import Foundation.CubeSlabGauge
import Mathlib.Probability.Kernel.WithDensity

/-! Actual ground-normalized stationary law for the homogeneous unit Wilson slab.
The eigenfunction is constructed, not assumed. No uniform spectral gap or
continuum theory follows from this finite-volume construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace OperatorDerivativeRewrite.Foundation.CubeSlabGround
open CubeTemporalSlab CubeWilsonSlab CubeSlabGauge

structure GroundData (beta : ℝ) where
  value : ℝ
  function : State → ℝ
  lower : ℝ
  upper : ℝ
  value_pos : 0 < value
  lower_pos : 0 < lower
  measurable : Measurable function
  bounds : ∀ U, lower ≤ function U ∧ |function U| ≤ upper
  eigen : ∀ U, (∫ V, CubeWilsonSlab.kernel beta U V*function V ∂boundaryHaar)=value*function U
  invariant : ∀ a U, function (gaugeAction a U)=function U

/-- An actual inhabitant follows from the previously constructed positive powers. -/
theorem ground_nonempty (beta : ℝ) : Nonempty (GroundData beta) := by
  obtain ⟨lam,psi,hl,hm,hb,he,hg⟩ := positive_ground_exists beta
  have hp (U : State) : 0 < psi U :=
    (div_pos (Real.exp_pos _) (Real.exp_pos _)).trans_le (hb U).1
  exact ⟨⟨lam,psi,_,_,hl,div_pos (Real.exp_pos _) (Real.exp_pos _),hm,
    fun U => ⟨(hb U).1,by rw [abs_of_pos (hp U)]; exact (hb U).2⟩,he,hg⟩⟩

/-- Choice from a proved nonempty type, not an existence axiom. -/
def ground (beta : ℝ) : GroundData beta := Classical.choice (ground_nonempty beta)

attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar


/-- A bounded-core pairing on the actual twelve-link product law. -/
def pairing (beta : ℝ) (f h : State → ℝ) : ℝ :=
  ∫ U, f U*(∫ V, CubeWilsonSlab.kernel beta U V*h V ∂boundaryHaar) ∂boundaryHaar

private theorem joint_integrable (beta : ℝ) (f h : State → ℝ)
    (hf : Measurable f) (hh : Measurable h) (B C : ℝ)
    (hB : ∀ U, |f U| ≤ B) (hC : ∀ U, |h U| ≤ C) :
    Integrable (fun q : State × State => f q.1*(CubeWilsonSlab.kernel beta q.1 q.2*h q.2))
      (boundaryHaar.prod boundaryHaar) := by
  apply Integrable.of_bound ((hf.comp measurable_fst).mul
    ((kernel_joint_measurable beta).mul (hh.comp measurable_snd))).aestronglyMeasurable
    (|B| *(Real.exp (36*|beta|)*|C|))
  filter_upwards with q
  change ‖f q.1*(CubeWilsonSlab.kernel beta q.1 q.2*h q.2)‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_pos (kernel_positive beta _ _)]
  exact mul_le_mul ((hB _).trans (le_abs_self _))
    (mul_le_mul (kernel_bounds beta _ _).2 ((hC _).trans (le_abs_self _))
      (abs_nonneg _) (Real.exp_pos _).le)
    (mul_nonneg (kernel_positive beta _ _).le (abs_nonneg _)) (abs_nonneg _)

theorem pairing_symmetric (beta : ℝ) (f h : State → ℝ)
    (hf : Measurable f) (hh : Measurable h) (B C : ℝ)
    (hB : ∀ U, |f U| ≤ B) (hC : ∀ U, |h U| ≤ C) :
    pairing beta f h=pairing beta h f := by
  unfold pairing
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap (joint_integrable beta f h hf hh B C hB hC)]
  apply integral_congr_ae
  filter_upwards with V
  apply integral_congr_ae
  filter_upwards with U
  rw [kernel_symmetric beta U V]
  ring

namespace GroundData
variable {beta : ℝ} (g : GroundData beta)

theorem function_pos (U : State) : 0 < g.function U :=
  g.lower_pos.trans_le (g.bounds U).1

theorem square_integrable : Integrable (fun U => g.function U^2) boundaryHaar := by
  apply Integrable.of_bound (g.measurable.pow_const 2).aestronglyMeasurable (g.upper^2)
  filter_upwards with U
  rw [Real.norm_eq_abs,abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (g.bounds U).2 2

def normalizer : ℝ := ∫ U, g.function U^2 ∂boundaryHaar

theorem normalizer_pos : 0 < g.normalizer := by
  have h := integral_mono (integrable_const (g.lower^2)) g.square_integrable
    (fun U => pow_le_pow_left₀ g.lower_pos.le (g.bounds U).1 2)
  simp only [integral_const,probReal_univ,one_smul] at h
  exact lt_of_lt_of_le (sq_pos_of_pos g.lower_pos) h

private theorem square_mass : SignedDensityProbabilitySampling.mass boundaryHaar
    (fun U => g.function U^2)=g.normalizer := by
  unfold SignedDensityProbabilitySampling.mass normalizer
  apply integral_congr_ae
  filter_upwards with U
  exact abs_of_nonneg (sq_nonneg _)

def stationary : Measure State :=
  SignedDensityProbabilitySampling.sampler boundaryHaar (fun U => g.function U^2)

theorem stationary_probability : IsProbabilityMeasure g.stationary :=
  SignedDensityProbabilitySampling.sampler_probability boundaryHaar _ g.square_integrable
    (by rw [g.square_mass]; exact g.normalizer_pos)

theorem stationary_integral (f : State → ℝ) :
    (∫ U, f U ∂g.stationary)=(∫ U, g.function U^2*f U ∂boundaryHaar)/g.normalizer := by
  have h := YMPositiveKernel.positive_sampler_integral boundaryHaar (fun U => g.function U^2) f
    (g.measurable.pow_const 2) (fun U => sq_nonneg _)
    (by rw [g.square_mass]; exact g.normalizer_pos)
  rw [g.square_mass] at h
  exact h

/-- Ground normalization, including the eigenvalue, relative to boundary Haar. -/
def density (U V : State) : ℝ :=
  CubeWilsonSlab.kernel beta U V*g.function V/(g.value*g.function U)

theorem density_pos (U V : State) : 0 < g.density U V :=
  div_pos (mul_pos (kernel_positive beta U V) (g.function_pos V))
    (mul_pos g.value_pos (g.function_pos U))

theorem density_measurable : Measurable (Function.uncurry g.density) := by
  unfold density Function.uncurry
  exact ((kernel_joint_measurable beta).mul (g.measurable.comp measurable_snd)).div
    (measurable_const.mul (g.measurable.comp measurable_fst))

private theorem weighted_integrable (U : State) :
    Integrable (fun V => CubeWilsonSlab.kernel beta U V*g.function V) boundaryHaar := by
  apply Integrable.of_bound (((kernel_joint_measurable beta).comp
    (measurable_const.prodMk measurable_id)).mul g.measurable).aestronglyMeasurable
    (Real.exp (36*|beta|)*|g.upper|)
  filter_upwards with V
  change ‖CubeWilsonSlab.kernel beta U V*g.function V‖ ≤ _
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (kernel_positive beta U V)]
  exact mul_le_mul (kernel_bounds beta U V).2 ((g.bounds V).2.trans (le_abs_self _))
    (abs_nonneg _) (Real.exp_pos _).le

theorem density_integrable (U : State) : Integrable (g.density U) boundaryHaar :=
  (g.weighted_integrable U).div_const _

theorem density_integral (U : State) : (∫ V, g.density U V ∂boundaryHaar)=1 := by
  unfold density
  rw [integral_div,g.eigen,div_self (mul_pos g.value_pos (g.function_pos U)).ne']

/-- A genuine measurable probability transition, not merely a scalar formula. -/
def transition : Kernel State State :=
  (Kernel.const State boundaryHaar).withDensity (fun U V => ENNReal.ofReal (g.density U V))

theorem transition_apply (U : State) :
    g.transition U=boundaryHaar.withDensity (fun V => ENNReal.ofReal (g.density U V)) :=
  Kernel.withDensity_apply _ g.density_measurable.ennreal_ofReal U

theorem transition_markov : IsMarkovKernel g.transition := by
  constructor
  intro U
  constructor
  rw [g.transition_apply,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (g.density_integrable U)
      (ae_of_all _ (fun V => (g.density_pos U V).le)),g.density_integral]
  norm_num

theorem transition_integral (f : State → ℝ) (U : State) :
    (∫ V, f V ∂g.transition U)=
      (∫ V, CubeWilsonSlab.kernel beta U V*(g.function V*f V) ∂boundaryHaar)/
        (g.value*g.function U) := by
  rw [g.transition_apply,integral_withDensity_eq_integral_toReal_smul
    ((Measurable.of_uncurry_left g.density_measurable).ennreal_ofReal)
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (g.density_pos _ _).le,smul_eq_mul]
  have he (V : State) : g.density U V*f V=
      (CubeWilsonSlab.kernel beta U V*(g.function V*f V))/(g.value*g.function U) := by
    unfold density; ring
  simp_rw [he]
  exact integral_div _ _

/-- Pointwise detailed balance density; actual stationarity is proved below. -/
theorem balance_density (U V : State) :
    g.function U^2*g.density U V=g.function V^2*g.density V U := by
  unfold density
  rw [kernel_symmetric beta V U]
  field_simp [(g.function_pos U).ne',(g.function_pos V).ne',g.value_pos.ne']

/-- Gauge invariance holds separately in each endpoint. -/
theorem density_gauge_left (a : Gauge) (U V : State) :
    g.density (gaugeAction a U) V=g.density U V := by
  unfold density
  rw [kernel_left_invariant,g.invariant]

theorem density_gauge_right (a : Gauge) (U V : State) :
    g.density U (gaugeAction a V)=g.density U V := by
  unfold density
  rw [kernel_right_invariant,g.invariant]


theorem stationary_pairing (f h : State → ℝ) :
    (∫ U, f U*(∫ V, h V ∂g.transition U) ∂g.stationary)=
      pairing beta (fun U => g.function U*f U) (fun U => g.function U*h U)/
        (g.value*g.normalizer) := by
  rw [g.stationary_integral]
  simp_rw [g.transition_integral]
  have he (U : State) : g.function U^2*(f U*((∫ V,
      CubeWilsonSlab.kernel beta U V*(g.function V*h V) ∂boundaryHaar)/
      (g.value*g.function U)))=
      ((g.function U*f U)*(∫ V, CubeWilsonSlab.kernel beta U V*
        (g.function V*h V) ∂boundaryHaar))/g.value := by
    field_simp [(g.function_pos U).ne',g.value_pos.ne']
  simp_rw [he]
  rw [integral_div]
  unfold pairing
  ring

/-- Stationarity on every bounded measurable probe of the constructed probability law. -/
theorem transition_stationary (f : State → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ U, |f U| ≤ B) :
    (∫ U, ∫ V, f V ∂g.transition U ∂g.stationary)=∫ U, f U ∂g.stationary := by
  have hp := g.stationary_pairing (fun _ => 1) f
  simp only [mul_one,one_mul] at hp
  rw [hp,pairing_symmetric beta g.function (fun U => g.function U*f U)
    g.measurable (g.measurable.mul hf) g.upper (|g.upper| * |B|)
    (fun U => (g.bounds U).2) (fun U => by
      rw [abs_mul]
      exact mul_le_mul ((g.bounds U).2.trans (le_abs_self _))
        ((hb U).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _))]
  unfold pairing
  simp_rw [g.eigen]
  have he (U : State) : (g.function U*f U)*(g.value*g.function U)=
      g.value*(g.function U^2*f U) := by ring
  simp_rw [he]
  rw [integral_const_mul,g.stationary_integral]
  field_simp [g.value_pos.ne',g.normalizer_pos.ne']

/-- Reversibility for the actual probability transition on a bounded core. -/
theorem stationary_reversible (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (B C : ℝ) (hB : ∀ U, |f U| ≤ B) (hC : ∀ U, |h U| ≤ C) :
    (∫ U, f U*(∫ V, h V ∂g.transition U) ∂g.stationary)=
      ∫ U, h U*(∫ V, f V ∂g.transition U) ∂g.stationary := by
  rw [g.stationary_pairing,g.stationary_pairing]
  congr 1
  apply pairing_symmetric beta _ _ (g.measurable.mul hf) (g.measurable.mul hh)
    (|g.upper| * |B|) (|g.upper| * |C|)
  · intro U
    simp only [Pi.mul_apply]
    rw [abs_mul]
    exact mul_le_mul ((g.bounds U).2.trans (le_abs_self _))
      ((hB U).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)
  · intro U
    simp only [Pi.mul_apply]
    rw [abs_mul]
    exact mul_le_mul ((g.bounds U).2.trans (le_abs_self _))
      ((hC U).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

end GroundData
end OperatorDerivativeRewrite.Foundation.CubeSlabGround
