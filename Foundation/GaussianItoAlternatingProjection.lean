import Foundation.GaussianItoSourceHodge
import Foundation.GaussianPotentialIteration
import Foundation.GaussianSensitivityGeometry

/-! Uniform convergence of actual causal/gradient alternating projections to first-chaos Ito fields. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianItoAlternatingProjection
open InfiniteGaussian GaussianNumberSectors GaussianConditionalGraph GaussianBrownianGeneratedSpace
open GaussianInverseNumberPotential GaussianPotentialIteration GaussianSourceHodge
open GaussianPredictableFull GaussianPredictableAdjoint GaussianBrownianPRP GaussianItoSourceHodge
open GaussianDivergenceRecovery
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : CompleteSpace fullPredictable := fullPredictable_isClosed.completeSpace_coe

def alternatingOperator : fullPredictable →L[ℝ] fullPredictable :=
  predictableProjection.comp (gradientProjection.comp predictableField.toContinuousLinearMap)

def firstChaosOperator : fullPredictable →L[ℝ] fullPredictable :=
  predictableAdjoint.comp ((projection 1).comp itoIntegral.toContinuousLinearMap)

def predictableFieldProjection : GaussianVectorL2 →L[ℝ] GaussianVectorL2 :=
  predictableField.toContinuousLinearMap.comp predictableProjection

theorem alternating_apply (u : fullPredictable) :
    alternatingOperator u=predictableAdjoint (potentialOperator (itoIntegral u)) := by
  change predictableProjection (gradientProjection (predictableField u))=_
  rw [ito_gradientProjection,predictable_recovery_potential]

theorem potential_brownian {f : GaussianL2} (hf : f∈brownianL2) : potentialOperator f∈brownianL2 :=
  potential_preserves_generated
    (fun t => SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
      (GaussianTimeHilbert.timeVector t)) hf

theorem integral_adjoint_centered {f : GaussianL2} (hf : f∈brownianL2) (h0 : projection 0 f=0) :
    itoIntegral (predictableAdjoint f)=f := by
  have he := brownian_representation f hf
  rw [← gaussianOne_inner_eq_integral,← projection_zero,h0,sub_zero] at he
  exact he

theorem integral_alternating (u : fullPredictable) :
    itoIntegral (alternatingOperator u)=potentialOperator (itoIntegral u) := by
  rw [alternating_apply]
  apply integral_adjoint_centered (potential_brownian (itoIntegral_mem_brownianL2 u))
  rw [projection_potential]
  simp

theorem integral_firstChaos (u : fullPredictable) :
    itoIntegral (firstChaosOperator u)=projection 1 (itoIntegral u) := by
  change itoIntegral (predictableAdjoint (projection 1 (itoIntegral u)))=_
  apply integral_adjoint_centered (projection_preserves_brownian 1 (itoIntegral_mem_brownianL2 u))
  exact projection_zero_positive 1 (by omega) _

theorem firstChaosOperator_idempotent (u : fullPredictable) : firstChaosOperator (firstChaosOperator u)=firstChaosOperator u := by
  change predictableAdjoint (projection 1 (itoIntegral (firstChaosOperator u)))=_
  rw [integral_firstChaos,projection_idempotent]
  rfl

theorem firstChaosOperator_inner (u v : fullPredictable) :
    inner ℝ (firstChaosOperator u) v=inner ℝ u (firstChaosOperator v) := by
  change inner ℝ (itoIntegral.toContinuousLinearMap.adjoint (projection 1 (itoIntegral u))) v=_
  rw [ContinuousLinearMap.adjoint_inner_left]
  change _=inner ℝ u (itoIntegral.toContinuousLinearMap.adjoint (projection 1 (itoIntegral v)))
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact (sector 1).inner_starProjection_left_eq_right _ _

theorem iterate_integral (k : ℕ) (u : fullPredictable) :
    itoIntegral ((alternatingOperator^k) u)=(potentialOperator^k) (itoIntegral u) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',pow_succ']
    change itoIntegral (alternatingOperator ((alternatingOperator^k) u))=
      potentialOperator ((potentialOperator^k) (itoIntegral u))
    rw [integral_alternating,ih]

theorem iterate_firstChaos_error (k : ℕ) (u : fullPredictable) :
    ‖(alternatingOperator^k) u-firstChaosOperator u‖≤(1/2 : ℝ)^k*‖u‖ := by
  rw [← itoIntegral.norm_map ((alternatingOperator^k) u-firstChaosOperator u),map_sub,
    iterate_integral,integral_firstChaos]
  simpa only [itoIntegral.norm_map] using iterate_first_error k (itoIntegral u)

theorem iterate_opNorm_error (k : ℕ) : ‖alternatingOperator^k-firstChaosOperator‖≤(1/2 : ℝ)^k := by
  apply ContinuousLinearMap.opNorm_le_bound (alternatingOperator^k-firstChaosOperator) (by positivity)
  intro u
  exact iterate_firstChaos_error k u

theorem alternating_operator_tendsto : Tendsto (fun k : ℕ => alternatingOperator^k) atTop (𝓝 firstChaosOperator) := by
  have ht : Tendsto (fun k : ℕ => ‖alternatingOperator^k-firstChaosOperator‖) atTop (𝓝 (0 : ℝ)) := by
    exact squeeze_zero (fun k => norm_nonneg (alternatingOperator^k-firstChaosOperator)) iterate_opNorm_error
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)<1))
  exact (tendsto_iff_norm_sub_tendsto_zero
    (f := fun k : ℕ => alternatingOperator^k) (a := atTop) (b := firstChaosOperator)).mpr ht

theorem predictableFieldProjection_field (u : fullPredictable) :
    predictableFieldProjection (predictableField u)=predictableField u := by
  change predictableField (predictableProjection (predictableField u))=_
  rw [show predictableProjection (predictableField u)=u from
    GaussianSensitivityGeometry.predictableProjection_field u]

theorem hodge_predictable_noncommutation :
    gradientProjection.comp predictableFieldProjection≠predictableFieldProjection.comp gradientProjection := by
  intro hcomm
  let u := terminalWickIntegrand 1 1
  have hm : itoIntegral u∈sector 2 := by
    rw [show u=terminalWickIntegrand 1 1 from rfl,terminalWickIntegrand_integral]
    exact IBMCubicFirstChaos.wick_mem_sector _ _
  have ha := alternating_projection_sector u 2 hm
  rw [ito_gradientProjection] at ha
  have he := congrArg (fun L : GaussianVectorL2 →L[ℝ] GaussianVectorL2 => L (predictableField u)) hcomm
  change gradientProjection (predictableFieldProjection (predictableField u))=
    predictableFieldProjection (gradientProjection (predictableField u)) at he
  rw [predictableFieldProjection_field,ito_gradientProjection] at he
  change recovery (itoIntegral u)=predictableField (predictableProjection (recovery (itoIntegral u))) at he
  rw [ha,map_smul] at he
  have hr := recovery_sector_energy 2 ⟨itoIntegral u,hm⟩
  have hu := terminalWickIntegrand_energy 1 1
  change ‖u‖^2=_ at hu
  rw [itoIntegral.norm_map,he,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,predictableField.norm_map] at hr
  norm_num at hu hr
  norm_num [hr] at hu

end OperatorDerivativeRewrite.Foundation.GaussianItoAlternatingProjection
