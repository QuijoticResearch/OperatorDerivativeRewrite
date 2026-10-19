import Foundation.IBMClockOverlapEnergy
import Foundation.GaussianTimeFieldNorm
import Foundation.ProductL2Curry
import Foundation.BochnerL2Fubini

/-! Actual Bochner-L2 candidates for the clock derivative of time-averaged IBM.
The construction and covariance identities do not assert a closed derivative graph. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace OperatorDerivativeRewrite.Foundation.IBMClockAverageCandidate
open InfiniteGaussian SeparableHilbertEmbedding GaussianTimeHilbert GaussianTimeProcess
open IBMFoldedTransitionBound IBMClockOverlapEnergy IBMGaussianSteinMoments
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable timeHilbert_secondCountable
attribute [local irreducible] IBMConstructedSources.clockPath
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def tensorBilinear : CoefficientSpace →L[ℝ] GaussianL2 →L[ℝ] GaussianVectorL2 :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip.compLpL₂ 2 gaussianProduct

theorem tensorBilinear_eq (h : CoefficientSpace) (f : GaussianL2) :
    tensorBilinear h f = scalarTensor h f := by
  apply Lp.ext
  filter_upwards [((ContinuousLinearMap.lsmul ℝ ℝ).flip h).coeFn_compLp f,
    scalarTensor_coeFn h f] with ω ht hs
  exact ht.trans hs.symm

theorem scalarTensor_joint_continuous :
    Continuous (fun p : CoefficientSpace × GaussianL2 => scalarTensor p.1 p.2) := by
  simp_rw [← tensorBilinear_eq]
  exact (tensorBilinear.continuous.comp continuous_fst).clm_apply continuous_snd

theorem scalarTensor_norm (h : CoefficientSpace) (f : GaussianL2) :
    ‖scalarTensor h f‖ = ‖f‖ * ‖h‖ := by
  have he : ‖scalarTensor h f‖ ^ 2 = (‖f‖ * ‖h‖) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, GaussianTimeFieldNorm.scalarTensor_pair_inner,
      real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  nlinarith [norm_nonneg (scalarTensor h f), mul_nonneg (norm_nonneg f) (norm_nonneg h)]

attribute [local irreducible] scalarTensor

def direction (t : ℝ) : CoefficientSpace := hilbertEmbedding TimeHilbert (timeVector t.toNNReal)

theorem direction_continuous : Continuous direction := by
  apply firstChaosEmbedding.isometry.comp_continuous_iff.mp
  change Continuous (fun t : ℝ => wienerL2 t.toNNReal)
  exact GaussianLipschitzIntegrands.wienerL2_continuous.comp continuous_real_toNNReal

theorem direction_norm_sq (t : ℝ) : ‖direction t‖ ^ 2 = (t.toNNReal : ℝ) := by
  rw [direction, (hilbertEmbedding TimeHilbert).norm_map, timeVector_norm_sq]

theorem direction_inner {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    inner ℝ (direction s) (direction t) = min s t := by
  rw [direction, direction, (hilbertEmbedding TimeHilbert).inner_map_map,
    timeVector_inner, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht]

def sourceColumn (n : ℕ) (r : ℝ) : GaussianL2 := firstChaosEmbedding (tripleCoefficient n r 1)

theorem sourceColumn_continuous (n : ℕ) : Continuous (sourceColumn n) :=
  firstChaosEmbedding.continuous.comp (IBMClockCubicTimeProjection.tripleCoefficient_continuous n 1)

theorem sourceColumn_inner (n m : ℕ) (r q : ℝ) :
    inner ℝ (sourceColumn n r) (sourceColumn m q) = overlap n m r q := by
  rw [sourceColumn, sourceColumn, firstChaosEmbedding.inner_map_map,
    overlap_eq_coefficient_inner]

theorem sourceColumn_bounded (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖sourceColumn n r‖ ≤ C := by
  obtain ⟨M, hM0, hM⟩ := overlap_bounded n n
  refine ⟨Real.sqrt M, Real.sqrt_nonneg _, fun r => ?_⟩
  have he : ‖sourceColumn n r‖ ^ 2 = overlap n n r r := by
    rw [← real_inner_self_eq_norm_sq, sourceColumn_inner]
  nlinarith [hM r r, Real.sq_sqrt hM0, norm_nonneg (sourceColumn n r), Real.sqrt_nonneg M]

attribute [local irreducible] sourceColumn direction

def sectionField (n : ℕ) (t : ℝ) (ω : SampleSpace) : GaussianVectorL2 :=
  BrownianSignIntegral.signum (IBMConstructedSources.clockPath ω t.toNNReal) •
    scalarTensor (direction t) (sourceColumn n |IBMConstructedSources.clockPath ω t.toNNReal|)

theorem section_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (Function.uncurry (sectionField n)) := by
  have hs : Measurable (fun p : ℝ × SampleSpace =>
      BrownianSignIntegral.signum (IBMConstructedSources.clockPath p.2 p.1.toNNReal)) :=
    BrownianSignIntegral.signum_measurable.comp BrownianClockWeightedEnergy.sigma_measurable
  have hd : StronglyMeasurable (fun p : ℝ × SampleSpace => direction p.1) :=
    direction_continuous.stronglyMeasurable.comp_measurable measurable_fst
  have hc : StronglyMeasurable (fun p : ℝ × SampleSpace =>
      sourceColumn n |IBMConstructedSources.clockPath p.2 p.1.toNNReal|) :=
    (sourceColumn_continuous n).stronglyMeasurable.comp_measurable
      (continuous_abs.measurable.comp BrownianClockWeightedEnergy.sigma_measurable)
  exact hs.stronglyMeasurable.smul (scalarTensor_joint_continuous.comp_stronglyMeasurable (hd.prodMk hc))

theorem section_norm_bound (n : ℕ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ r, ‖sourceColumn n r‖ ≤ C) (t : ℝ) (ω : SampleSpace) :
    ‖sectionField n t ω‖ ≤ C * ‖direction t‖ := by
  rw [sectionField, norm_smul, scalarTensor_norm]
  calc
    _ ≤ 1 * (C * ‖direction t‖) := mul_le_mul
      (BrownianSignIntegral.signum_bound _) (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := one_mul _

theorem section_memLp (n : ℕ) (t : ℝ) : MemLp (sectionField n t) 2 gaussianProduct := by
  obtain ⟨C, hC, hb⟩ := sourceColumn_bounded n
  apply MemLp.of_bound ((section_stronglyMeasurable n).comp_measurable
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable (C * ‖direction t‖)
  exact ae_of_all _ (section_norm_bound n hC hb t)

abbrev Target := Lp GaussianVectorL2 2 gaussianProduct

def field (n : ℕ) (t : ℝ) : Target :=
  ProductL2Sections.sectionL2 gaussianProduct (Function.uncurry (sectionField n)) t

theorem field_ae (n : ℕ) (t : ℝ) : field n t =ᵐ[gaussianProduct] sectionField n t :=
  ProductL2Sections.sectionL2_coeFn gaussianProduct _ t (section_memLp n t)

theorem field_stronglyMeasurable (n : ℕ) : StronglyMeasurable (field n) :=
  ProductL2Sections.sectionL2_stronglyMeasurable gaussianProduct _ (section_stronglyMeasurable n)

theorem field_norm_bound (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r, ‖sourceColumn n r‖ ≤ C) (t : ℝ) : ‖field n t‖ ≤ C * ‖direction t‖ := by
  have h := Lp.norm_le_of_ae_bound (f := field n t) (mul_nonneg hC (norm_nonneg (direction t)))
    ((field_ae n t).mono fun ω hω => hω ▸ section_norm_bound n hC hb t ω)
  simpa [measureUnivNNReal] using h

theorem section_inner (n m : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (ω : SampleSpace) :
    inner ℝ (sectionField n s ω) (sectionField m t ω) = min s t * signedColumn n m ((s,t),ω) := by
  rw [sectionField, sectionField, real_inner_smul_left, inner_smul_right,
    GaussianTimeFieldNorm.scalarTensor_pair_inner, sourceColumn_inner, direction_inner hs ht]
  unfold signedColumn
  ring

theorem field_inner (n m : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    inner ℝ (field n s) (field m t) = signedEnergyKernel n m s t := by
  rw [L2_inner_eq_integral]
  calc
    _ = ∫ ω, min s t * signedColumn n m ((s,t),ω) ∂gaussianProduct := by
      apply integral_congr_ae
      filter_upwards [field_ae n s, field_ae m t] with ω hn hm
      rw [hn, hm, section_inner n m hs ht]
    _ = _ := by rw [integral_const_mul]; rfl

theorem sourceColumn_actual_ae (n : ℕ) (r : ℝ) : sourceColumn n r =ᵐ[gaussianProduct]
    fun ω => IBMDyadicExtension.field n 1 ω r := by
  simpa only [sourceColumn, gaussianTriple_eq_firstChaos] using
    (IBMDyadicExtension.field_coordinate_ae n 1 r).symm

theorem sectionField_actual_ae (n : ℕ) (t : ℝ) (ωY : SampleSpace) :
    sectionField n t ωY =ᵐ[gaussianProduct] fun ωX =>
      (BrownianSignIntegral.signum (IBMConstructedSources.clockPath ωY t.toNNReal) *
        IBMConstructedSources.mollifiedValue n 1 t.toNNReal (ωX,ωY)) • direction t := by
  filter_upwards [Lp.coeFn_smul
      (BrownianSignIntegral.signum (IBMConstructedSources.clockPath ωY t.toNNReal))
      (scalarTensor (direction t) (sourceColumn n |IBMConstructedSources.clockPath ωY t.toNNReal|)),
    scalarTensor_coeFn (direction t) (sourceColumn n |IBMConstructedSources.clockPath ωY t.toNNReal|),
    sourceColumn_actual_ae n |IBMConstructedSources.clockPath ωY t.toNNReal|] with ωX hs ht hc
  change (BrownianSignIntegral.signum _ • scalarTensor _ _) ωX = _
  rw [hs, Pi.smul_apply, ht, hc, smul_smul]
  rfl

theorem field_actual_ae (n : ℕ) (t : ℝ) : ∀ᵐ ωY ∂gaussianProduct,
    field n t ωY =ᵐ[gaussianProduct] fun ωX =>
      (BrownianSignIntegral.signum (IBMConstructedSources.clockPath ωY t.toNNReal) *
        IBMConstructedSources.mollifiedValue n 1 t.toNNReal (ωX,ωY)) • direction t := by
  filter_upwards [field_ae n t] with ωY hY
  rw [hY]
  exact sectionField_actual_ae n t ωY

theorem direction_norm_bound {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ Ioc 0 T) :
    ‖direction t‖ ≤ Real.sqrt T := by
  have hn := direction_norm_sq t
  rw [Real.coe_toNNReal _ ht.1.le] at hn
  nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T, norm_nonneg (direction t), ht.2]

theorem field_integrable (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (field n) (window T) := by
  obtain ⟨C, hC, hb⟩ := sourceColumn_bounded n
  apply Integrable.of_bound (field_stronglyMeasurable n).aestronglyMeasurable (C * Real.sqrt T)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (field_norm_bound n hC hb t).trans
    (mul_le_mul_of_nonneg_left (direction_norm_bound hT ht) hC)

def average (n : ℕ) (T : ℝ) : Target := ∫ t, field n t ∂window T

/-- The actual Hilbert inner product of two constructed averaged fields equals
the signed covariance integral, including different spatial mollifier widths. -/
theorem average_inner (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    inner ℝ (average n T) (average m T) =
      ∫ p : ℝ × ℝ, signedEnergyKernel n m p.1 p.2 ∂(window T).prod (window T) := by
  rw [average, average, real_inner_comm, ← integral_inner (field_integrable n hT),
    integral_prod _ (signedEnergyKernel_integrable n m hT)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [real_inner_comm, ← integral_inner (field_integrable m hT)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [field_inner n m hs.1.le ht.1.le]

theorem average_norm_sq (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖average n T‖ ^ 2 =
      ∫ p : ℝ × ℝ, signedEnergyKernel n n p.1 p.2 ∂(window T).prod (window T) := by
  rw [← real_inner_self_eq_norm_sq, average_inner n n hT]

/-- Uniform bound for genuine Bochner-L2 averaged candidate fields. No closed
Malliavin derivative graph is inferred from this norm bound. -/
theorem average_uniform_energy (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖average n T‖ ^ 2 ≤ 8 * peak 1 * T ^ 2 * Real.sqrt T := by
  rw [average_norm_sq n hT]
  apply le_trans ?_ (signedEnergyKernel_integral_norm_bound n n hT)
  apply integral_mono (signedEnergyKernel_integrable n n hT)
    (signedEnergyKernel_integrable n n hT).norm
  intro p
  exact le_abs_self _

def pointwiseAverage (n : ℕ) (T : ℝ) (ω : SampleSpace) : GaussianVectorL2 :=
  ∫ t, sectionField n t ω ∂window T

theorem pointwiseAverage_stronglyMeasurable (n : ℕ) (T : ℝ) :
    StronglyMeasurable (pointwiseAverage n T) :=
  (section_stronglyMeasurable n).integral_prod_left' (μ := window T)

theorem pointwiseAverage_bound (n : ℕ) {C T : ℝ} (hC : 0 ≤ C)
    (hb : ∀ r, ‖sourceColumn n r‖ ≤ C) (hT : 0 ≤ T) (ω : SampleSpace) :
    ‖pointwiseAverage n T ω‖ ≤ T * (C * Real.sqrt T) := by
  have hp : ∀ᵐ t ∂window T, ‖sectionField n t ω‖ ≤ C * Real.sqrt T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (section_norm_bound n hC hb t ω).trans
      (mul_le_mul_of_nonneg_left (direction_norm_bound hT ht) hC)
  have h := norm_integral_le_of_norm_le_const hp
  simpa [pointwiseAverage, window, Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal hT, mul_comm] using h

theorem pointwiseAverage_memLp (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    MemLp (pointwiseAverage n T) 2 gaussianProduct := by
  obtain ⟨C, hC, hb⟩ := sourceColumn_bounded n
  exact MemLp.of_bound (pointwiseAverage_stronglyMeasurable n T).aestronglyMeasurable
    (T * (C * Real.sqrt T)) (ae_of_all _ (pointwiseAverage_bound n hC hb hT))

/-- A justified outer-clock representative formula for the Bochner average.
The inner values are actual source-Gaussian vector-L2 classes. -/
theorem average_ae (n : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    average n T =ᵐ[gaussianProduct] pointwiseAverage n T := by
  obtain ⟨C, hC, hb⟩ := sourceColumn_bounded n
  have hmem : ∀ᵐ p : ℝ × SampleSpace ∂(window T).prod gaussianProduct, p.1 ∈ Ioc 0 T :=
    (Measure.quasiMeasurePreserving_fst (μ := window T) (ν := gaussianProduct)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hbound : ∀ᵐ p : ℝ × SampleSpace ∂(window T).prod gaussianProduct,
      ‖sectionField n p.1 p.2‖ ≤ C * Real.sqrt T := by
    filter_upwards [hmem] with p hp
    exact (section_norm_bound n hC hb p.1 p.2).trans
      (mul_le_mul_of_nonneg_left (direction_norm_bound hT hp) hC)
  let W : Target := (pointwiseAverage_memLp n hT).toLp (pointwiseAverage n T)
  have he : average n T = W :=
    BochnerL2Fubini.integral_eq_of_slices (field n) (field_integrable n hT)
      (Function.uncurry (sectionField n)) (section_stronglyMeasurable n).aestronglyMeasurable
      (ae_of_all _ (field_ae n)) (fun _ : SampleSpace => C * Real.sqrt T)
      (memLp_const _) hbound W (MemLp.coeFn_toLp _)
  rw [he]
  exact MemLp.coeFn_toLp _

/-- Exact mixed-width distance formula for the constructed L2 averages. It
reduces a possible strong Cauchy proof to the actual cross-covariance energies. -/
theorem average_distance_sq (n m : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    ‖average n T - average m T‖ ^ 2 =
      ∫ p : ℝ × ℝ, (signedEnergyKernel n n p.1 p.2 + signedEnergyKernel m m p.1 p.2 -
        2 * signedEnergyKernel n m p.1 p.2) ∂(window T).prod (window T) := by
  have he := integral_sub
    ((signedEnergyKernel_integrable n n hT).add (signedEnergyKernel_integrable m m hT))
    ((signedEnergyKernel_integrable n m hT).const_mul 2)
  simp only [Pi.add_apply] at he
  have ha := integral_add (signedEnergyKernel_integrable n n hT) (signedEnergyKernel_integrable m m hT)
  rw [ha, integral_const_mul] at he
  rw [he, norm_sub_sq_real, average_norm_sq n hT, average_norm_sq m hT, average_inner n m hT]
  ring

end OperatorDerivativeRewrite.Foundation.IBMClockAverageCandidate
