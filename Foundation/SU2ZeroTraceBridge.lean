import Foundation.SU2WilsonSignCrossing
import Foundation.SU2WilsonConvolution
import Mathlib.Probability.Kernel.Composition.Comp

/-! A genuine two-step Haar reset through a zero-trace band for the actual
trace-product loop kernel. No Wilson-lattice identification is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
open OperatorDerivativeRewrite.Foundation.SU2InteractingLoopKernel
open OperatorDerivativeRewrite.Foundation.MeasurableExponentialKernel

namespace OperatorDerivativeRewrite.Foundation.SU2ZeroTraceBridge

def band (δ : ℝ) : Set SU2 := {C | |halfTrace C| < δ}

theorem band_measurable (δ : ℝ) : MeasurableSet (band δ) :=
  by simpa only [band, Real.norm_eq_abs] using measurableSet_lt halfTrace_measurable.norm measurable_const

private theorem trace_continuous : Continuous halfTrace := by
  have he : halfTrace = fun A : SU2 => ((A : SU2TraceHessianModel.M2) 0 0).re / 2 + ((A : SU2TraceHessianModel.M2) 1 1).re / 2 := by
    funext A
    simp [halfTrace, SU2TraceHessianModel.traceReal, Matrix.trace_fin_two, add_div]
  rw [he]
  have hentry (i j : Fin 2) : Continuous (fun A : SU2 => (A : SU2TraceHessianModel.M2) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact (((Complex.continuous_re.comp (hentry 0 0)).div_const 2).add
    ((Complex.continuous_re.comp (hentry 1 1)).div_const 2))

theorem band_mass_pos (δ : ℝ) (hδ : 0 < δ) : 0 < law.real (band δ) := by
  have ho : IsOpen (band δ) := isOpen_lt trace_continuous.abs continuous_const
  let C := SU2WilsonSignCrossing.left 0 1 (by norm_num)
  have hz : halfTrace C = 0 := SU2WilsonSignCrossing.left_trace 0 1 _
  have hm : C ∈ band δ := by simpa [band, hz] using hδ
  have hp : 0 < law (band δ) := IsOpen.measure_pos law ho ⟨C, hm⟩
  exact ENNReal.toReal_pos hp.ne' (measure_lt_top _ _).ne

private theorem small_product (δ : ℝ) (C Z : SU2) (hZ : Z ∈ band δ) :
    |halfTrace C * halfTrace Z| ≤ δ := by
  rw [abs_mul]
  have h := mul_le_mul (halfTrace_bound C) (le_of_lt hZ) (abs_nonneg (halfTrace Z))
    (by norm_num : (0 : ℝ) ≤ 1)
  simpa using h

private theorem interaction_lower (r δ : ℝ) (hr : 0 ≤ r) (C Z : SU2)
    (hZ : Z ∈ band δ) : -(r * δ) ≤ interaction r C Z := by
  have hp : -δ ≤ halfTrace C * halfTrace Z :=
    (neg_le_neg (small_product δ C Z hZ)).trans (neg_abs_le _)
  have hm := mul_le_mul_of_nonneg_left hp hr
  simpa [interaction, mul_assoc] using hm

/-- Arrival in the central band costs at most exp((1 + δ)r) pointwise. -/
theorem density_into_band (r δ : ℝ) (hr : 0 ≤ r) (C Z : SU2)
    (hZ : Z ∈ band δ) :
    Real.exp (-(r * (1 + δ))) ≤ density law (interaction r) C Z := by
  have hp := partition_positive law (interaction r) C (interaction_exp_integrable r C)
  have hu := partition_upper r C
  rw [abs_of_nonneg hr] at hu
  apply (le_div_iff₀ hp).mpr
  calc
    Real.exp (-(r * (1 + δ))) * partition law (interaction r) C ≤
        Real.exp (-(r * (1 + δ))) * Real.exp r :=
      mul_le_mul_of_nonneg_left hu (Real.exp_pos _).le
    _ = Real.exp (-(r * δ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (interaction r C Z) := Real.exp_le_exp.mpr (interaction_lower r δ hr C Z hZ)

private theorem band_partition_upper (r δ : ℝ) (hr : 0 ≤ r) (Z : SU2)
    (hZ : Z ∈ band δ) : partition law (interaction r) Z ≤ Real.exp (r * δ) := by
  have h := integral_mono (interaction_exp_integrable r Z) (integrable_const (Real.exp (r * δ)))
    (fun D => Real.exp_le_exp.mpr (show interaction r Z D ≤ r * δ by
      have hs := small_product δ D Z hZ
      have hb : halfTrace Z * halfTrace D ≤ δ := by
        rw [mul_comm]
        exact (le_abs_self _).trans hs
      simpa [interaction, mul_assoc] using mul_le_mul_of_nonneg_left hb hr))
  simpa [partition] using h

/-- Departing from the central band has a nearly unbiased Haar component. -/
theorem density_from_band (r δ : ℝ) (hr : 0 ≤ r) (Z D : SU2)
    (hZ : Z ∈ band δ) :
    Real.exp (-(2 * r * δ)) ≤ density law (interaction r) Z D := by
  have hp := partition_positive law (interaction r) Z (interaction_exp_integrable r Z)
  apply (le_div_iff₀ hp).mpr
  calc
    Real.exp (-(2 * r * δ)) * partition law (interaction r) Z ≤
        Real.exp (-(2 * r * δ)) * Real.exp (r * δ) :=
      mul_le_mul_of_nonneg_left (band_partition_upper r δ hr Z hZ) (Real.exp_pos _).le
    _ = Real.exp (-(r * δ)) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (interaction r Z D) := by
      apply Real.exp_le_exp.mpr
      have h := interaction_lower r δ hr D Z hZ
      simpa [interaction, mul_comm, mul_left_comm, mul_assoc] using h

theorem band_hit (r δ : ℝ) (hr : 0 ≤ r) (C : SU2) :
    ENNReal.ofReal (Real.exp (-(r * (1 + δ)))) * law (band δ) ≤ loopKernel r C (band δ) := by
  rw [loopKernel, kernel_apply law _ (interaction_measurable r),
    withDensity_apply _ (band_measurable δ)]
  have h := setLIntegral_mono (μ := law)
    ((density_measurable law (interaction r) (interaction_measurable r)).of_uncurry_left.ennreal_ofReal)
    (fun Z hZ => ENNReal.ofReal_le_ofReal (density_into_band r δ hr C Z hZ))
  simpa only [lintegral_const, Measure.restrict_apply_univ, mul_comm] using h

theorem band_reset (r δ : ℝ) (hr : 0 ≤ r) (Z : SU2) (hZ : Z ∈ band δ) :
    ENNReal.ofReal (Real.exp (-(2 * r * δ))) • law ≤ loopKernel r Z := by
  rw [loopKernel, kernel_apply law _ (interaction_measurable r)]
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards with D
  exact ENNReal.ofReal_le_ofReal (density_from_band r δ hr Z D hZ)

/-- The coefficient is explicit and positive for every nonempty band. -/
def bridge (r δ : ℝ) : ℝ := law.real (band δ) * Real.exp (-(1 + 3 * δ) * r)

theorem bridge_pos (r δ : ℝ) (hδ : 0 < δ) : 0 < bridge r δ :=
  mul_pos (band_mass_pos δ hδ) (Real.exp_pos _)

/-- Actual composition of the existing probability kernel, not a surrogate
matrix or a hypothetical transition density. -/
theorem two_step_reset (r δ : ℝ) (hr : 0 ≤ r) (C : SU2) :
    ENNReal.ofReal (bridge r δ) • law ≤ (loopKernel r ∘ₖ loopKernel r) C := by
  apply Measure.le_iff.mpr
  intro B hB
  rw [Measure.smul_apply, smul_eq_mul, Kernel.comp_apply' _ _ _ hB]
  have hband := band_hit r δ hr C
  have hlow :
      ENNReal.ofReal (Real.exp (-(2 * r * δ))) * law B * loopKernel r C (band δ) ≤
        ∫⁻ Z, loopKernel r Z B ∂loopKernel r C := by
    calc
      _ = ∫⁻ Z in band δ, ENNReal.ofReal (Real.exp (-(2 * r * δ))) * law B ∂loopKernel r C := by
        rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ Z in band δ, loopKernel r Z B ∂loopKernel r C := by
        apply setLIntegral_mono ((loopKernel r).measurable_coe hB)
        intro Z hZ
        have hm := band_reset r δ hr Z hZ
        have he := hm B
        simpa only [Measure.smul_apply, smul_eq_mul] using he
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hmul := mul_le_mul_of_nonneg_left hband
    (show 0 ≤ ENNReal.ofReal (Real.exp (-(2 * r * δ))) * law B from bot_le)
  apply le_trans ?_ hlow
  apply le_trans ?_ hmul
  have hb : ENNReal.ofReal (law.real (band δ)) = law (band δ) :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hex : Real.exp (-(1 + 3 * δ) * r) = Real.exp (-(2 * r * δ)) * Real.exp (-(r * (1 + δ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [bridge, hex, ENNReal.ofReal_mul measureReal_nonneg, hb,
    ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact le_of_eq (by ring)

theorem bridge_le_one (r δ : ℝ) (hr : 0 ≤ r) (C : SU2) : bridge r δ ≤ 1 := by
  haveI := loopKernel_markov r
  have h := two_step_reset r δ hr C Set.univ
  simpa only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one,
    ENNReal.ofReal_le_one] using h

/-- Halving the proved reset gives a strictly positive residual weight. -/
def reset (r δ : ℝ) : ℝ := bridge r δ / 2

theorem reset_range (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ) :
    0 < reset r δ ∧ reset r δ < 1 := by
  have hp := bridge_pos r δ hδ
  have hu := bridge_le_one r δ hr 1
  dsimp [reset]
  constructor <;> linarith

private theorem reset_minorization (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ) (C : SU2) :
    ENNReal.ofReal (reset r δ) • law ≤ (loopKernel r ∘ₖ loopKernel r) C := by
  apply le_trans ?_ (two_step_reset r δ hr C)
  apply Measure.le_iff.mpr
  intro B hB
  simp only [Measure.smul_apply, smul_eq_mul]
  apply mul_le_mul_of_nonneg_right ?_ bot_le
  apply ENNReal.ofReal_le_ofReal
  have hp := bridge_pos r δ hδ
  dsimp [reset]
  linarith

def twoAverage (r : ℝ) (f : SU2 → ℝ) (C : SU2) : ℝ :=
  ∫ D, f D ∂(loopKernel r ∘ₖ loopKernel r) C

private theorem unit_integrable (ν : Measure SU2) [IsProbabilityMeasure ν]
    (f : SU2 → ℝ) (hf : Measurable f) (hb : ∀ D, 0 ≤ f D ∧ f D ≤ 1) : Integrable f ν := by
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  filter_upwards with D
  simpa [Real.norm_eq_abs, abs_of_nonneg (hb D).1] using (hb D).2

theorem twoAverage_measurable (r : ℝ) (f : SU2 → ℝ) (hf : Measurable f) :
    Measurable (twoAverage r f) := hf.stronglyMeasurable.integral_kernel.measurable

/-- Residual range bounds are obtained directly from the actual measure
minorization; there is no appeal to a hypothetical stationary reset. -/
theorem twoAverage_bounds (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ)
    (f : SU2 → ℝ) (hf : Measurable f) (hb : ∀ D, 0 ≤ f D ∧ f D ≤ 1) (C : SU2) :
    reset r δ * (∫ D, f D ∂law) ≤ twoAverage r f C ∧
      twoAverage r f C ≤ reset r δ * (∫ D, f D ∂law) + 1 - reset r δ := by
  haveI := loopKernel_markov r
  have hi := unit_integrable ((loopKernel r ∘ₖ loopKernel r) C) f hf hb
  have hr0 := (reset_range r δ hr hδ).1.le
  have hm := reset_minorization r δ hr hδ C
  have hl := integral_mono_measure hm (Eventually.of_forall (fun D => (hb D).1)) hi
  rw [integral_smul_measure, ENNReal.toReal_ofReal hr0] at hl
  change reset r δ * (∫ D, f D ∂law) ≤ twoAverage r f C at hl
  have hg := integral_mono_measure (f := fun D => 1 - f D) hm
    (Eventually.of_forall (fun D => sub_nonneg.mpr (hb D).2)) ((integrable_const 1).sub hi)
  rw [integral_smul_measure, ENNReal.toReal_ofReal hr0,
    integral_sub (integrable_const 1) (unit_integrable law f hf hb),
    integral_sub (integrable_const 1) hi] at hg
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hg
  exact ⟨hl, by dsimp [twoAverage]; linarith⟩

private theorem twoAverage_affine (r a b : ℝ) (g : SU2 → ℝ)
    (hg : Measurable g) (hb : ∀ D, 0 ≤ g D ∧ g D ≤ 1) (C : SU2) :
    twoAverage r (fun D => a + b * g D) C = a + b * twoAverage r g C := by
  haveI := loopKernel_markov r
  unfold twoAverage
  rw [integral_add (integrable_const a) ((unit_integrable _ g hg hb).const_mul b),
    integral_const_mul]
  simp

/-- Iteration is of the actual composed kernel, twice per step. -/
def iterate (r : ℝ) : ℕ → (SU2 → ℝ) → SU2 → ℝ
  | 0, f => f
  | n + 1, f => twoAverage r (iterate r n f)

theorem iterate_measurable (r : ℝ) (n : ℕ) (f : SU2 → ℝ) (hf : Measurable f) :
    Measurable (iterate r n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact twoAverage_measurable r _ ih

/-- Range width contracts at every genuine pair of loop-kernel steps. -/
theorem iterate_range (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ)
    (n : ℕ) (f : SU2 → ℝ) (hf : Measurable f) (hb : ∀ D, 0 ≤ f D ∧ f D ≤ 1) :
    ∃ a : ℝ, ∀ C, a ≤ iterate r n f C ∧ iterate r n f C ≤ a + (1 - reset r δ)^n := by
  have hq : 0 < 1 - reset r δ := sub_pos.mpr (reset_range r δ hr hδ).2
  induction n with
  | zero => exact ⟨0, by simpa [iterate] using hb⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := ih
    let w := (1 - reset r δ)^n
    have hw : 0 < w := pow_pos hq n
    let g : SU2 → ℝ := fun D => (iterate r n f D - a)/w
    have hg : Measurable g := ((iterate_measurable r n f hf).sub_const a).div_const w
    have hgb (D : SU2) : 0 ≤ g D ∧ g D ≤ 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr (ha D).1) hw.le
      · apply (div_le_one hw).mpr
        change iterate r n f D - a ≤ (1 - reset r δ)^n
        linarith [(ha D).2]
    have he : iterate r n f = fun D => a + w * g D := by
      funext D
      dsimp [g]
      field_simp
      ring
    refine ⟨a + w * (reset r δ * (∫ D, g D ∂law)), ?_⟩
    intro C
    have ht := twoAverage_bounds r δ hr hδ g hg hgb C
    have hl := mul_le_mul_of_nonneg_left ht.1 hw.le
    have hu := mul_le_mul_of_nonneg_left ht.2 hw.le
    change a + w * (reset r δ * (∫ D, g D ∂law)) ≤ twoAverage r (iterate r n f) C ∧
      twoAverage r (iterate r n f) C ≤ a + w * (reset r δ * (∫ D, g D ∂law)) + (1 - reset r δ)^(n + 1)
    simp only [he, twoAverage_affine r a w g hg hgb C]
    rw [pow_succ]
    dsimp [w] at *
    constructor <;> nlinarith

theorem iterate_oscillation (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ)
    (n : ℕ) (f : SU2 → ℝ) (hf : Measurable f) (hb : ∀ D, 0 ≤ f D ∧ f D ≤ 1)
    (C D : SU2) : |iterate r n f C - iterate r n f D| ≤ (1 - reset r δ)^n := by
  obtain ⟨a,ha⟩ := iterate_range r δ hr hδ n f hf hb
  exact abs_le.mpr ⟨by linarith [(ha C).1,(ha D).2], by linarith [(ha D).1,(ha C).2]⟩

/-- Quantified recovery of bounded-observable contraction for actual iterates. -/
theorem iterate_exponential_bound (r δ t : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ)
    (n : ℕ) (hn : t ≤ (n : ℝ) * reset r δ) (f : SU2 → ℝ) (hf : Measurable f)
    (hb : ∀ D, 0 ≤ f D ∧ f D ≤ 1) (C D : SU2) :
    |iterate r n f C - iterate r n f D| ≤ Real.exp (-t) := by
  apply (iterate_oscillation r δ hr hδ n f hf hb C D).trans
  have hbase : 1 - reset r δ ≤ Real.exp (-reset r δ) := by
    linarith [Real.add_one_le_exp (-reset r δ)]
  have hp := pow_le_pow_left₀ (sub_pos.mpr (reset_range r δ hr hδ).2).le hbase n
  have he : Real.exp (-reset r δ)^n = Real.exp (-(n : ℝ) * reset r δ) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he] at hp
  exact hp.trans (Real.exp_le_exp.mpr (by linarith))

theorem twoAverage_eq_transfer_twice (r : ℝ) (f : SU2 → ℝ) (hf : Measurable f)
    (hb : ∀ D, 0 ≤ f D ∧ f D ≤ 1) (C : SU2) :
    twoAverage r f C = SU2VariationalGap.transfer r (SU2VariationalGap.transfer r f) C := by
  haveI := loopKernel_markov r
  exact Kernel.integral_comp (unit_integrable _ f hf hb)

/-- A concrete sufficient pair count; twice as many original transitions. -/
theorem sufficient_pair_count (r δ t : ℝ) (hδ : 0 < δ) (n : ℕ)
    (hn : (2 * t/law.real (band δ)) * Real.exp ((1 + 3 * δ) * r) ≤ (n : ℝ)) :
    t ≤ (n : ℝ) * reset r δ := by
  have hb := band_mass_pos δ hδ
  have hex : Real.exp ((1 + 3 * δ) * r) * Real.exp (-(1 + 3 * δ) * r) = 1 := by
    rw [← Real.exp_add, show (1 + 3 * δ) * r + -(1 + 3 * δ) * r = 0 by ring, Real.exp_zero]
  have he : ((2 * t/law.real (band δ)) * Real.exp ((1 + 3 * δ) * r)) * reset r δ = t := by
    calc
      _ = t * (Real.exp ((1 + 3 * δ) * r) * Real.exp (-(1 + 3 * δ) * r)) := by
        dsimp [reset, bridge]
        field_simp [hb.ne']
      _ = t := by rw [hex, mul_one]
  rw [← he]
  exact mul_le_mul_of_nonneg_right hn (div_pos (bridge_pos r δ hδ) (by norm_num)).le

/-- A positive contraction on an explicitly PROPOSED distance scale. No
identification of this scale with the physical Yang--Mills spacing is supplied. -/
theorem proposed_distance_oscillation (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 < δ)
    (n : ℕ) (f : SU2 → ℝ) (hf : Measurable f) (hb : ∀ D, 0 ≤ f D ∧ f D ≤ 1)
    (C D : SU2) : |iterate r n f C - iterate r n f D| ≤
      Real.exp (-((law.real (band δ)/4) * ((2 * (n : ℝ)) * Real.exp (-(1 + 3 * δ) * r)))) := by
  apply iterate_exponential_bound r δ _ hr hδ n ?_ f hf hb C D
  dsimp [reset, bridge]
  exact le_of_eq (by ring)

/-- The trace-product loop has an exact Haar row at every zero-trace state. -/
theorem zero_trace_row (r : ℝ) (C : SU2) (hC : halfTrace C = 0) : loopKernel r C = law := by
  rw [loopKernel_section, hC, mul_zero]
  exact SU2StapleExtremes.zero_tilt law halfTrace

/-- The actual Wilson row retains its relative-holonomy first moment even when
the absolute trace of the current state is zero. -/
theorem wilson_relative_mean (β : ℝ) (C : SU2) :
    (∫ D, halfTrace (C⁻¹ * D) ∂SU2OneWordTransfer.transition law β C⁻¹) =
      SU2WilsonConvolution.coefficient β := by
  have h := SU2WilsonConvolution.step_actual_kernel β (fun D : SU2 => halfTrace (C⁻¹ * D))
    (halfTrace_measurable.comp (measurable_const_mul C⁻¹)) C
  simpa [SU2WilsonConvolution.step, SU2WilsonConvolution.coefficient, mul_assoc] using h.symm

/-- A proved obstruction to identifying the central-band mechanism with Wilson
transport. This is already a finite one-word counterexample, not a4D theorem. -/
theorem zero_trace_wilson_mismatch : ∀ᶠ β : ℝ in atTop,
    ∃ C : SU2, halfTrace C = 0 ∧ loopKernel β C = law ∧
      SU2OneWordTransfer.transition law β C⁻¹ ≠ law := by
  have ht : Tendsto SU2WilsonConvolution.coefficient atTop (𝓝 1) :=
    SU2OneWordLargeCoupling.positive_mean_tendsto_one
  have hp := (tendsto_order.mp ht).1 (1 / 2) (by norm_num)
  filter_upwards [hp] with β hβ
  let C := SU2WilsonSignCrossing.left 0 1 (by norm_num)
  have hC : halfTrace C = 0 := SU2WilsonSignCrossing.left_trace 0 1 _
  refine ⟨C, hC, zero_trace_row β C hC, ?_⟩
  intro he
  have hm := wilson_relative_mean β C
  rw [he, integral_mul_left_eq_self halfTrace C⁻¹,
    (SU2TiltEnergyResponse.moment_values law).1] at hm
  linarith

/-- Every exponent strictly larger than one is available, with an explicit
positive band-mass prefactor depending on the chosen exponent. -/
theorem reset_rate_near_one (η : ℝ) (hη : 0 < η) :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℝ, 0 ≤ r → ∀ C : SU2,
      ENNReal.ofReal (b * Real.exp (-(1 + η) * r)) • law ≤ (loopKernel r ∘ₖ loopKernel r) C := by
  refine ⟨law.real (band (η / 3)), band_mass_pos (η / 3) (by positivity), ?_⟩
  intro r hr C
  have he : bridge r (η / 3) = law.real (band (η / 3)) * Real.exp (-(1 + η) * r) := by
    unfold bridge
    congr 1
    congr 1
    ring
  rw [← he]
  exact two_step_reset r (η / 3) hr C

end OperatorDerivativeRewrite.Foundation.SU2ZeroTraceBridge
