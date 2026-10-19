import Foundation.IBMClockObservationGraph
import Foundation.BochnerL2Approximation

/-! Assembly of source-first-chaos scalar clock graphs in the genuine product L2.
The scalar product flip is the already verified probability-factor isometry. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFirstSourceClockGraph
open InfiniteGaussian
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

abbrev ScalarSpace := Lp GaussianL2 2 gaussianProduct
abbrev VectorSpace := Lp GaussianVectorL2 2 gaussianProduct

def projection (N : ℕ) : GaussianL2 →L[ℝ] GaussianL2 :=
  ∑ i ∈ Finset.range N, (ContinuousLinearMap.toSpanSingleton ℝ (coordinateL2 i)).comp
    (innerSL ℝ (coordinateL2 i))

theorem projection_apply (N : ℕ) (f : GaussianL2) :
    projection N f = ∑ i ∈ Finset.range N, inner ℝ (coordinateL2 i) f • coordinateL2 i := by
  simp [projection]

theorem projection_norm_le (N : ℕ) (f : GaussianL2) : ‖projection N f‖ ≤ ‖f‖ := by
  have he : ‖projection N f‖ ^ 2 =
      ∑ i ∈ Finset.range N, ‖inner ℝ (coordinateL2 i) f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, projection_apply]
    simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right,
      orthonormal_iff_ite.mp coordinateL2_orthonormal]
    simp only [mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_range,
      Real.norm_eq_abs, sq_abs, pow_two]
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
    simp only [← pow_two, sq_abs]
  have hb := coordinateL2_orthonormal.sum_inner_products_le (s := Finset.range N) f
  nlinarith [norm_nonneg (projection N f), norm_nonneg f]

theorem coordinate_embedding_inner (i : ℕ) (b : CoefficientSpace) :
    inner ℝ (coordinateL2 i) (firstChaosEmbedding b) = b i := by
  have he : coordinateL2 i = firstChaosEmbedding (lp.single 2 i (1 : ℝ)) := by
    rw [firstChaos_single, one_smul]
  rw [he, firstChaos_inner]
  simp [lp.inner_single_left]

theorem projection_embedding_tendsto (b : CoefficientSpace) :
    Tendsto (fun N => projection N (firstChaosEmbedding b)) atTop (𝓝 (firstChaosEmbedding b)) := by
  simpa only [projection_apply, coordinate_embedding_inner] using (firstChaos_hasSum b).tendsto_sum_nat

def projected (N : ℕ) : ScalarSpace →L[ℝ] ScalarSpace :=
  (projection N).compLpL 2 gaussianProduct

theorem projected_tendsto (u : ScalarSpace)
    (hu : ∀ᵐ ω ∂gaussianProduct, u ω ∈ firstChaosEmbedding.toLinearMap.range) :
    Tendsto (fun N => projected N u) atTop (𝓝 u) := by
  apply BochnerL2Dominated.tendsto_of_ae_norm_bound
  · intro N
    filter_upwards [(projection N).coeFn_compLpL u] with ω hω
    change projected N u ω = projection N (u ω) at hω
    rw [hω]
    exact projection_norm_le _ _
  · have ha := ae_all_iff.mpr (fun N => (projection N).coeFn_compLpL u)
    filter_upwards [ha, hu] with ω ha hu
    obtain ⟨b, hb⟩ := hu
    have he : (fun N => projected N u ω) = fun N => projection N (firstChaosEmbedding b) := by
      funext N
      change (projection N).compLpL 2 gaussianProduct u ω = _
      rw [ha N, ← hb]
      rfl
    rw [he, ← hb]
    exact projection_embedding_tendsto b

def coordinate (i : ℕ) : ScalarSpace →L[ℝ] GaussianL2 :=
  (innerSL ℝ (coordinateL2 i)).compLpL 2 gaussianProduct

theorem projected_sum (N : ℕ) (u : ScalarSpace) :
    projected N u = ∑ i ∈ Finset.range N,
      BochnerClosedOperator.tensor gaussianProduct (coordinate i u) (coordinateL2 i) := by
  apply Lp.ext
  have ha := ae_all_iff.mpr (fun i => (innerSL ℝ (coordinateL2 i)).coeFn_compLpL u)
  have ht := ae_all_iff.mpr (fun i => BochnerClosedOperator.tensor_coeFn gaussianProduct
    (coordinate i u) (coordinateL2 i))
  filter_upwards [(projection N).coeFn_compLpL u, ha, ht,
    Lp.coeFn_fun_finsetSum (Finset.range N) (fun i =>
      BochnerClosedOperator.tensor gaussianProduct (coordinate i u) (coordinateL2 i))]
    with ω hp ha ht hs
  change projected N u ω = _ at hp
  rw [hp, projection_apply, hs]
  apply Finset.sum_congr rfl
  intro i hi
  rw [ht i]
  change _ = coordinate i u ω • coordinateL2 i
  have hai : coordinate i u ω = inner ℝ (coordinateL2 i) (u ω) := ha i
  rw [hai]

def flip : ScalarSpace →ₗᵢ[ℝ] ScalarSpace := ProductL2Curry.flip gaussianProduct gaussianProduct

attribute [local irreducible] flip scalarTensor

theorem flip_tensor (a v : GaussianL2) :
    flip (BochnerClosedOperator.tensor gaussianProduct a v) =
      BochnerClosedOperator.tensor gaussianProduct v a := by
  unfold flip
  exact ProductL2Curry.flip_tensor _ _ _ _

def gradientMap (h : CoefficientSpace) : ScalarSpace →L[ℝ] VectorSpace :=
  (IBMClockAverageCandidate.tensorBilinear h).compLpL 2 gaussianProduct

set_option maxHeartbeats 800000 in
/-- Scalar source coordinates with genuine clock graphs assemble to a full
source/clock Bochner graph when both source sections are in first chaos. -/
theorem assembled_graph (u w : ScalarSpace) (h : CoefficientSpace)
    (hu : ∀ᵐ ω ∂gaussianProduct, u ω ∈ firstChaosEmbedding.toLinearMap.range)
    (hw : ∀ᵐ ω ∂gaussianProduct, w ω ∈ firstChaosEmbedding.toLinearMap.range)
    (hg : ∀ i, (coordinate i u, scalarTensor h (coordinate i w)) ∈ closedCylindricalDerivative.graph) :
    (flip u, gradientMap h (flip w)) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph := by
  have htU := flip.continuous.continuousAt.tendsto.comp (projected_tendsto u hu)
  have htW := (gradientMap h).continuous.continuousAt.tendsto.comp
    (flip.continuous.continuousAt.tendsto.comp (projected_tendsto w hw))
  apply (BochnerClosedOperator.lift_isClosed gaussianProduct closedCylindricalDerivative
    closedCylindricalDerivative_isClosed).mem_of_tendsto (htU.prodMk_nhds htW)
  apply Eventually.of_forall
  intro N
  dsimp only [Function.comp_def]
  rw [projected_sum, projected_sum, map_sum, map_sum, map_sum]
  have he (i : ℕ) : flip (BochnerClosedOperator.tensor gaussianProduct (coordinate i u) (coordinateL2 i)) =
      BochnerClosedOperator.tensor gaussianProduct (coordinateL2 i) (coordinate i u) :=
    flip_tensor _ _
  have hf (i : ℕ) : gradientMap h
      (flip (BochnerClosedOperator.tensor gaussianProduct (coordinate i w) (coordinateL2 i))) =
      BochnerClosedOperator.tensor gaussianProduct (coordinateL2 i) (scalarTensor h (coordinate i w)) := by
    rw [show flip (BochnerClosedOperator.tensor gaussianProduct (coordinate i w) (coordinateL2 i)) =
      BochnerClosedOperator.tensor gaussianProduct (coordinateL2 i) (coordinate i w) from
        flip_tensor _ _]
    apply Lp.ext
    filter_upwards [(IBMClockAverageCandidate.tensorBilinear h).coeFn_compLpL
        (BochnerClosedOperator.tensor gaussianProduct (coordinateL2 i) (coordinate i w)),
      BochnerClosedOperator.tensor_coeFn gaussianProduct (coordinateL2 i) (coordinate i w),
      BochnerClosedOperator.tensor_coeFn gaussianProduct (coordinateL2 i) (scalarTensor h (coordinate i w))]
      with ω hl ht hs
    change gradientMap h _ ω = _ at hl
    rw [hl, ht, map_smul, IBMClockAverageCandidate.tensorBilinear_eq, hs]
  simp_rw [he, hf]
  rw [prod_mk_sum]
  apply (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph.sum_mem
  intro i hi
  exact BochnerClosedOperator.tensor_graph gaussianProduct
    closedCylindricalDerivative (coordinateL2 i) _ _ (hg i)

attribute [local irreducible] IBMConstructedSources.clockPath

def signedSourceClass (n : ℕ) (t : ℝ≥0) (ω : SampleSpace) : GaussianL2 :=
  BrownianSignIntegral.signum (IBMConstructedSources.clockPath ω t) •
    IBMClockAverageCandidate.sourceColumn n |IBMConstructedSources.clockPath ω t|

theorem signedSourceClass_stronglyMeasurable (n : ℕ) (t : ℝ≥0) :
    StronglyMeasurable (signedSourceClass n t) := by
  have hm : Measurable (fun ω => IBMConstructedSources.clockPath ω t) := by
    have h := BrownianClockWeightedEnergy.sigma_measurable.comp
      (show Measurable (fun ω : SampleSpace => ((t : ℝ), ω)) from
        measurable_const.prodMk measurable_id)
    simpa only [Function.comp_def, BrownianClockWeightedEnergy.sigma, Real.toNNReal_coe] using h
  exact (BrownianSignIntegral.signum_measurable.comp hm).stronglyMeasurable.smul
    ((IBMClockAverageCandidate.sourceColumn_continuous n).stronglyMeasurable.comp_measurable
      (continuous_abs.measurable.comp hm))

theorem signedSourceClass_memLp (n : ℕ) (t : ℝ≥0) :
    MemLp (signedSourceClass n t) 2 gaussianProduct := by
  obtain ⟨C, hC, hb⟩ := IBMClockAverageCandidate.sourceColumn_bounded n
  apply MemLp.of_bound (signedSourceClass_stronglyMeasurable n t).aestronglyMeasurable C
  apply ae_of_all
  intro ω
  rw [signedSourceClass, norm_smul]
  exact (mul_le_mul_of_nonneg_right (BrownianSignIntegral.signum_bound _) (norm_nonneg _)).trans
    (by simpa using hb _)

def signedSource (n : ℕ) (t : ℝ≥0) : ScalarSpace :=
  (signedSourceClass_memLp n t).toLp _

theorem signedSource_ae (n : ℕ) (t : ℝ≥0) :
    signedSource n t =ᵐ[gaussianProduct] signedSourceClass n t :=
  (signedSourceClass_memLp n t).coeFn_toLp

theorem signedSource_firstChaos (n : ℕ) (t : ℝ≥0) :
    ∀ᵐ ω ∂gaussianProduct, signedSource n t ω ∈ firstChaosEmbedding.toLinearMap.range := by
  filter_upwards [signedSource_ae n t] with ω hω
  rw [hω]
  refine ⟨BrownianSignIntegral.signum (IBMConstructedSources.clockPath ω t) •
    IBMGaussianSteinMoments.tripleCoefficient n |IBMConstructedSources.clockPath ω t| 1, ?_⟩
  change firstChaosEmbedding _ = _
  rw [map_smul]
  rfl

theorem mollified_firstChaos (n : ℕ) (t : ℝ≥0) :
    ∀ᵐ ω ∂gaussianProduct, IBMRandomTimeHilbert.randomMollifiedL2 n t ω ∈
      firstChaosEmbedding.toLinearMap.range := by
  filter_upwards [(IBMRandomTimeHilbert.randomMollifiedClass_memLp n t).coeFn_toLp] with ω hω
  change IBMRandomTimeHilbert.randomMollifiedL2 n t ω =
    IBMRandomTimeHilbert.randomMollifiedClass n t ω at hω
  rw [hω]
  refine ⟨IBMGaussianSteinMoments.tripleCoefficient n |GaussianTimeProcess.process t ω| 0, ?_⟩
  have he := IBMOriginalBoundaryResidual.triple_embedding n |GaussianTimeProcess.process t ω| 0
  simp only [IBMJointMollifierGaussian.derivativeKernel, ↓reduceIte] at he
  exact he

theorem coordinate_clock_graph (n : ℕ) (t : ℝ≥0) (ht : 0 < t) (i : ℕ) :
    (coordinate i (IBMRandomTimeHilbert.randomMollifiedL2 n t),
      scalarTensor (IBMClockAverageCandidate.direction t) (coordinate i (signedSource n t))) ∈
        closedCylindricalDerivative.graph := by
  obtain ⟨F, G, hfg, hF, hG⟩ :=
    IBMClockObservationGraph.reflected_actual_clock_graph t ht n (coordinateL2 i)
  have hFi : coordinate i (IBMRandomTimeHilbert.randomMollifiedL2 n t) = F := by
    apply Lp.ext
    filter_upwards [(innerSL ℝ (coordinateL2 i)).coeFn_compLpL
        (IBMRandomTimeHilbert.randomMollifiedL2 n t),
      (IBMRandomTimeHilbert.randomMollifiedClass_memLp n t).coeFn_toLp,
      IBMConstructedSources.clockPath_coordinate_ae t, hF] with ω hc hu hy hf
    change coordinate i (IBMRandomTimeHilbert.randomMollifiedL2 n t) ω =
      inner ℝ (coordinateL2 i) (IBMRandomTimeHilbert.randomMollifiedL2 n t ω) at hc
    change IBMRandomTimeHilbert.randomMollifiedL2 n t ω =
      IBMRandomTimeHilbert.randomMollifiedClass n t ω at hu
    rw [hc, hu, hf]
    change inner ℝ (coordinateL2 i)
      (IBMContinuousScenery.wholeLineScenery (IBMMollifier.kernel n) |GaussianTimeProcess.process t ω|) = _
    rw [hy]
  have hGi : scalarTensor (IBMClockAverageCandidate.direction t) (coordinate i (signedSource n t)) = G := by
    apply Lp.ext
    filter_upwards [scalarTensor_coeFn (IBMClockAverageCandidate.direction t) (coordinate i (signedSource n t)),
      (innerSL ℝ (coordinateL2 i)).coeFn_compLpL (signedSource n t),
      signedSource_ae n t, hG] with ω ht hc hs hg
    change coordinate i (signedSource n t) ω = inner ℝ (coordinateL2 i) (signedSource n t ω) at hc
    rw [ht, hc, hs, hg]
    simp only [signedSourceClass, real_inner_smul_right, mul_comm]
  rw [hFi, hGi]
  exact hfg

def clockGradient (n : ℕ) (t : ℝ≥0) : VectorSpace :=
  gradientMap (IBMClockAverageCandidate.direction t) (flip (signedSource n t))

/-- Actual joint partial clock graph, with the source sample outside and the
clock sample inside, obtained by strong limits of genuine separated graphs. -/
theorem mollified_clock_graph (n : ℕ) (t : ℝ≥0) (ht : 0 < t) :
    (flip (IBMRandomTimeHilbert.randomMollifiedL2 n t), clockGradient n t) ∈
      (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph :=
  assembled_graph _ _ _ (mollified_firstChaos n t) (signedSource_firstChaos n t)
    (coordinate_clock_graph n t ht)

theorem gradientMap_inner (h k : CoefficientSpace) (u v : ScalarSpace) :
    inner ℝ (gradientMap h u) (gradientMap k v) = inner ℝ u v * inner ℝ h k := by
  rw [L2.inner_def, L2.inner_def]
  have he : (∫ ω, inner ℝ (gradientMap h u ω) (gradientMap k v ω) ∂gaussianProduct) =
      ∫ ω, inner ℝ (u ω) (v ω) * inner ℝ h k ∂gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [(IBMClockAverageCandidate.tensorBilinear h).coeFn_compLpL u,
      (IBMClockAverageCandidate.tensorBilinear k).coeFn_compLpL v] with ω hu hv
    change gradientMap h u ω = IBMClockAverageCandidate.tensorBilinear h (u ω) at hu
    change gradientMap k v ω = IBMClockAverageCandidate.tensorBilinear k (v ω) at hv
    rw [hu, hv, IBMClockAverageCandidate.tensorBilinear_eq,
      IBMClockAverageCandidate.tensorBilinear_eq, GaussianTimeFieldNorm.scalarTensor_pair_inner]
  rw [he, integral_mul_const]

theorem candidate_eq_gradientMap (n : ℕ) (t : ℝ≥0) :
    IBMClockAverageCandidate.field n t =
      gradientMap (IBMClockAverageCandidate.direction t) (signedSource n t) := by
  apply Lp.ext
  filter_upwards [IBMClockAverageCandidate.field_ae n t,
    (IBMClockAverageCandidate.tensorBilinear (IBMClockAverageCandidate.direction t)).coeFn_compLpL
      (signedSource n t), signedSource_ae n t] with ω hf hg hs
  change gradientMap (IBMClockAverageCandidate.direction t) (signedSource n t) ω =
    IBMClockAverageCandidate.tensorBilinear (IBMClockAverageCandidate.direction t) (signedSource n t ω) at hg
  rw [hf, hg, hs]
  simp only [signedSourceClass, map_smul, IBMClockAverageCandidate.tensorBilinear_eq,
    IBMClockAverageCandidate.sectionField, Real.toNNReal_coe]

/-- The genuine joint clock derivative has exactly the candidate mixed energies,
despite the opposite order of its two probability factors. -/
theorem clockGradient_inner (n m : ℕ) (t s : ℝ≥0) :
    inner ℝ (clockGradient n t) (clockGradient m s) =
      inner ℝ (IBMClockAverageCandidate.field n t) (IBMClockAverageCandidate.field m s) := by
  rw [clockGradient, clockGradient, gradientMap_inner, flip.inner_map_map,
    candidate_eq_gradientMap, candidate_eq_gradientMap, gradientMap_inner]

theorem clockGradient_norm (n : ℕ) (t : ℝ≥0) :
    ‖clockGradient n t‖ = ‖IBMClockAverageCandidate.field n t‖ := by
  have he := clockGradient_inner n n t t
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at he
  nlinarith [norm_nonneg (clockGradient n t), norm_nonneg (IBMClockAverageCandidate.field n t)]

end OperatorDerivativeRewrite.Foundation.IBMFirstSourceClockGraph
