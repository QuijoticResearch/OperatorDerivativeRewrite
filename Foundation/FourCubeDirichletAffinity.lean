import Foundation.FourCubeCubicStability
import Foundation.FourCubeFullHaarAsymptotic
/-! Distinguish the72-face cap law from the actual864-face Dirichlet completion.
The extra48 interior penalties are not a boundary scalar. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeDirichletAffinity
open QuaternionSU2Representation FourCubeHaarParity
open FourCubeConditionalScore FourCubeHaarContinuousIntegral
attribute [local irreducible] OneSidedBlockIncidence.edges OneSidedBlockIncidence.upperFaces

def capAction (s : InteriorState) : ℝ := FourCubeIntegratedCubic.cellAction 0 0 0 s

def boxAction (s : InteriorState) : ℝ :=
  FourCubeDirichletBox.action (FourCubeCompletedHaar.angles 0 0 0) s

def capZ (β : ℝ) : ℝ := FourCubePinnedConcentration.normalizer β

def boxZ (β : ℝ) : ℝ := FourCubeCompletedHaar.standardPartition β (FourCubeCompletedHaar.angles 0 0 0)

private theorem axis_zero (a : Fin 3) : SU2JointPlaquetteCubic.axis a 0=1 := by
  apply Subtype.ext
  change (SU2JointPlaquetteCubic.axis a 0 : SU2TraceHessianModel.M2)=1
  rw [SU2AxisMatrixJets.axis_matrix_formula]
  simp

private theorem boundary_zero : FourCubeIntegratedCubic.boundaryData 0 0 0=fun _ => (1:SU2) := by
  funext c
  cases c <;> simp [FourCubeIntegratedCubic.boundaryData,axis_zero]

theorem capZ_eq_partition (β : ℝ) : capZ β=FourCubeBoundarySmoothPartition.partition β 0 := by
  rw [FourCubeBoundarySmoothPartition.partition_eq_actual,FourCubePinnedHaar.partition3_eq_pinned]
  change capZ β=FourCubePinnedHaar.pinnedPartition β (FourCubeIntegratedCubic.boundaryData 0 0 0)
  rw [boundary_zero]
  rfl

theorem capZ_integral (β : ℝ) : capZ β=∫ s,Real.exp (-β*capAction s) ∂interiorHaar := by
  rw [capZ_eq_partition,FourCubeBoundarySmoothPartition.partition_integral]
  rfl

theorem boxZ_integral (β : ℝ) : boxZ β=∫ s,Real.exp (-β*boxAction s) ∂interiorHaar := rfl

theorem capZ_pos (β : ℝ) : 0<capZ β := FourCubePinnedConcentration.normalizer_positive β

theorem boxZ_pos (β : ℝ) : 0<boxZ β := FourCubeCompletedHaar.standard_positive β _

theorem action_completion (s : InteriorState) :
    boxAction s=capAction s+FourCubeCompletedHaar.diagonal s := by
  rw [boxAction,FourCubeCompletedHaar.angles,FourCubeExteriorSources.full_angle_identity]
  simp only [Real.cos_zero,sub_self,mul_zero,add_zero,capAction,FourCubeCompletedHaar.diagonal]

/-- The lower-side terms depend on interior links and therefore do not cancel as scalar calibration. -/
theorem relative_weight (β : ℝ) (s : InteriorState) :
    Real.exp (-β*boxAction s)=Real.exp (-β*capAction s)*Real.exp (-β*FourCubeCompletedHaar.diagonal s) := by
  rw [action_completion,← Real.exp_add]
  congr 1
  ring

def capLimit : ℝ := ∫ Y : FourCubeHemisphereCoercivity.Field,FourCubeHaarLaplaceDensity.gaussianDensity Y

def boxLimit : ℝ := ∫ Y : FourCubeFullChartOdd.Coordinates,FourCubeFullHaarGaussianLimit.gaussianDensity 0 0 0 Y

theorem capLimit_pos : 0<capLimit := FourCubeHaarLaplaceDensity.gaussianDensity_integral_positive

theorem boxLimit_pos : 0<boxLimit := FourCubeFullHaarGaussianLimit.gaussian_integral_positive 0 0 0

theorem cap_asymptotic : Tendsto (fun t : ℝ => capZ (1/t^2)/|t|^93) (𝓝[≠] 0) (𝓝 capLimit) :=
  FourCubeHaarPartitionAsymptotic.actual_normalizer_asymptotic

theorem boxZ_eq_completed (β : ℝ) :
    boxZ β=FourCubeCompletedHaar.completedPartition β (FourCubeCompletedHaar.angles 0 0 0) := by
  rw [boxZ,FourCubeCompletedHaar.partition_factor,FourCubeCompletedHaar.sourceCost_angles]
  simp

theorem box_asymptotic : Tendsto (fun t : ℝ => boxZ (1/t^2)/|t|^96) (𝓝[≠] 0) (𝓝 boxLimit) := by
  have h := FourCubeFullHaarAsymptotic.full_partition_limit 0 0 0
  simpa only [boxZ_eq_completed,FourCubeFullHaarGaussianLimit.parameters,mul_zero,boxLimit] using h

theorem box_scaled_asymptotic (a : ℝ) (ha : 0<a) :
    Tendsto (fun t : ℝ => boxZ (a/t^2)/|t|^96) (𝓝[≠] 0)
      (𝓝 (boxLimit*(Real.sqrt a)⁻¹^96)) := by
  have hs : 0<Real.sqrt a := Real.sqrt_pos.mpr ha
  have hm : Tendsto (fun t : ℝ => t/Real.sqrt a) (𝓝[≠] 0) (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · simpa using ((tendsto_id.div_const (Real.sqrt a)).mono_left
        (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ)≤𝓝 0))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_ne_zero ht hs.ne'
  have hh := (box_asymptotic.comp hm).mul_const ((Real.sqrt a)⁻¹^96)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he : 1/(t/Real.sqrt a)^2=a/t^2 := by
    rw [div_pow,Real.sq_sqrt ha.le]
    field_simp
  change (boxZ (1/(t/Real.sqrt a)^2)/|t/Real.sqrt a|^96)*(Real.sqrt a)⁻¹^96=_
  rw [he,abs_div,abs_of_pos hs,div_pow]
  field_simp [hs.ne',abs_ne_zero.mpr ht]

/-- The exact completion costs three additional Gaussian powers. -/
theorem relative_partition_limit :
    Tendsto (fun t : ℝ => (boxZ (1/t^2)/capZ (1/t^2))/|t|^3) (𝓝[≠] 0) (𝓝 (boxLimit/capLimit)) := by
  have h := box_asymptotic.div cap_asymptotic capLimit_pos.ne'
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (boxZ (1/t^2)/|t|^96)/(capZ (1/t^2)/|t|^93)=(boxZ (1/t^2)/capZ (1/t^2))/|t|^3
  field_simp [(capZ_pos (1/t^2)).ne',abs_ne_zero.mpr ht]
  <;> ring

def capRoot (β : ℝ) (s : InteriorState) : ℝ := Real.exp (-β*capAction s/2)/Real.sqrt (capZ β)
def boxRoot (β : ℝ) (s : InteriorState) : ℝ := Real.exp (-β*boxAction s/2)/Real.sqrt (boxZ β)

theorem root_squares (β : ℝ) (s : InteriorState) :
    (capRoot β s)^2=Real.exp (-β*capAction s)/capZ β ∧
    (boxRoot β s)^2=Real.exp (-β*boxAction s)/boxZ β := by
  constructor
  · rw [capRoot,div_pow,Real.sq_sqrt (capZ_pos β).le,pow_two,← Real.exp_add]
    congr 2
    ring
  · rw [boxRoot,div_pow,Real.sq_sqrt (boxZ_pos β).le,pow_two,← Real.exp_add]
    congr 2
    ring

theorem cap_law_density (β : ℝ) :
    FourCubeConditionalScore.law β 0=interiorHaar.withDensity (fun s => ENNReal.ofReal ((capRoot β s)^2)) := by
  rw [FourCubeHaarHalfDensity.law_root_density]
  congr 1
  funext s
  rw [FourCubeHaarHalfDensity.root_sq,(root_squares β s).1,capZ_eq_partition,
    FourCubeBoundarySmoothAction.action_apply]
  rfl

theorem box_law_density (β : ℝ) :
    FourCubeScalarCalibration.standardLaw β (FourCubeCompletedHaar.angles 0 0 0)=
      interiorHaar.withDensity (fun s => ENNReal.ofReal ((boxRoot β s)^2)) := by
  unfold FourCubeScalarCalibration.standardLaw
  congr 1
  funext s
  rw [(root_squares β s).2]
  rfl

def halfWeight (β : ℝ) (s : InteriorState) : ℝ := Real.exp (-β*(capAction s+boxAction s)/2)
def halfPartition (β : ℝ) : ℝ := ∫ s,halfWeight β s ∂interiorHaar

theorem half_integrable (β : ℝ) (hβ : 0≤β) : Integrable (halfWeight β) interiorHaar := by
  have hm : Measurable (halfWeight β) := by
    unfold halfWeight capAction boxAction
    exact ((measurable_const.mul ((FourCubeIntegratedCubic.cellAction_measurable 0 0 0).add
      (FourCubeDirichletHaar.action_measurable _))).div_const 2).exp
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  filter_upwards with s
  change ‖Real.exp (-β*(capAction s+boxAction s)/2)‖≤1
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_one_iff.mpr
  have hC := (FourCubeIntegratedCubic.cellAction_bounds 0 0 0 s).1
  have hD := FourCubeDirichletBox.action_nonneg (FourCubeCompletedHaar.angles 0 0 0) s
  change -β*(capAction s+boxAction s)/2≤0
  change 0≤capAction s at hC
  change 0≤boxAction s at hD
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hβ) (add_nonneg hC hD)) (by norm_num)

theorem half_nonneg (β : ℝ) : 0≤halfPartition β := integral_nonneg (fun s => (Real.exp_pos _).le)

theorem half_le_box (β : ℝ) (hβ : 0≤β) : halfPartition β≤boxZ (β/2) := by
  rw [halfPartition,boxZ_integral]
  apply integral_mono (half_integrable β hβ) (FourCubeCompletedHaar.standard_integrable (β/2) _)
  intro s
  apply Real.exp_le_exp.mpr
  change -β*(capAction s+boxAction s)/2≤-(β/2)*boxAction s
  have hC : 0≤capAction s := (FourCubeIntegratedCubic.cellAction_bounds 0 0 0 s).1
  nlinarith [mul_nonneg hβ hC]

def affinity (β : ℝ) : ℝ := ∫ s,capRoot β s*boxRoot β s ∂interiorHaar

theorem affinity_eq (β : ℝ) :
    affinity β=halfPartition β/(Real.sqrt (capZ β)*Real.sqrt (boxZ β)) := by
  rw [affinity,halfPartition,← integral_div]
  apply integral_congr_ae
  filter_upwards with s
  rw [capRoot,boxRoot,div_mul_div_comm,← Real.exp_add]
  congr 2
  ring

theorem affinity_square_le (β : ℝ) (hβ : 0≤β) :
    (affinity β)^2≤(boxZ (β/2))^2/(capZ β*boxZ β) := by
  rw [affinity_eq,div_pow,mul_pow,Real.sq_sqrt (capZ_pos β).le,Real.sq_sqrt (boxZ_pos β).le]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (half_nonneg β) (half_le_box β hβ) 2)
    (mul_pos (capZ_pos β) (boxZ_pos β)).le

def affinityUpper (t : ℝ) : ℝ := (boxZ ((1/2)/t^2))^2/(capZ (1/t^2)*boxZ (1/t^2))

theorem affinityUpper_tendsto : Tendsto affinityUpper (𝓝[≠] 0) (𝓝 0) := by
  have hQ := ((box_scaled_asymptotic (1/2) (by norm_num)).pow 2).div
    (cap_asymptotic.mul box_asymptotic) (mul_pos capLimit_pos boxLimit_pos).ne'
  have hi : Tendsto (fun t : ℝ => |t|^3) (𝓝[≠] 0) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ)≤𝓝 0)).abs.pow 3)
  have hh := hi.mul hQ
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change |t|^3*((boxZ ((1/2)/t^2)/|t|^96)^2/
    ((capZ (1/t^2)/|t|^93)*(boxZ (1/t^2)/|t|^96)))=affinityUpper t
  unfold affinityUpper
  field_simp [(capZ_pos (1/t^2)).ne',(boxZ_pos (1/t^2)).ne',abs_ne_zero.mpr ht]
  <;> ring

/-- Actual normalized full-Haar densities, not Gaussian proxy laws, become orthogonal. -/
theorem affinity_square_tendsto :
    Tendsto (fun t : ℝ => (affinity (1/t^2))^2) (𝓝[≠] 0) (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (fun t => sq_nonneg (affinity (1/t^2)))) _ affinityUpper_tendsto
  filter_upwards with t
  have h := affinity_square_le (1/t^2) (by positivity)
  convert h using 1 <;> unfold affinityUpper <;> congr 2 <;> ring

theorem affinity_tendsto : Tendsto (fun t : ℝ => affinity (1/t^2)) (𝓝[≠] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [affinity_square_tendsto.eventually (eventually_lt_nhds (sq_pos_of_pos hε))] with t ht
  rw [Real.dist_eq,sub_zero]
  nlinarith [sq_abs (affinity (1/t^2)),abs_nonneg (affinity (1/t^2))]
end OperatorDerivativeRewrite.Foundation.FourCubeDirichletAffinity
