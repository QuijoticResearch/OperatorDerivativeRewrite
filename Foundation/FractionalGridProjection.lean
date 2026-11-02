import Foundation.StochasticCauchyFractionalDivergence
import Foundation.ContinuousFractionalPrediction

/-! Actual fractional two-cell field geometry. Cellwise conditional expectation
is tested at the LEFT grid times0,1, not relabeled as the manuscript's full
continuous-time predictable projection. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalGridProjection
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm
open StochasticCauchyFractionalDivergence GaussianConditionalGraph
variable (H : ℝ) (hH0 : 0<H) (hH1 : H<1)

def correlation : ℝ := inner ℝ (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1)
def pastField : GaussianVectorL2 := scalarTensor (fractionalPast H hH0 hH1)
  (FractionalGaussianProcess.value H hH0 hH1 1)
def incrementField : GaussianVectorL2 := scalarTensor (fractionalIncrement H hH0 hH1)
  (FractionalGaussianProcess.value H hH0 hH1 1)
def field (a b : ℝ) : GaussianVectorL2 := a • pastField H hH0 hH1+b • incrementField H hH0 hH1

private theorem past_unit : inner ℝ (fractionalPast H hH0 hH1) (fractionalPast H hH0 hH1)=1 := by
  simp only [fractionalPast,FractionalWickCovariance.direction_inner,FractionalSpectralGeometry.covariance]
  norm_num [Real.zero_rpow (by linarith : 2*H ≠ 0)]

private theorem increment_unit :
    inner ℝ (fractionalIncrement H hH0 hH1) (fractionalIncrement H hH0 hH1)=1 := by
  simp only [fractionalIncrement,fractionalPast,inner_sub_left,inner_sub_right,
    FractionalWickCovariance.direction_inner,FractionalSpectralGeometry.covariance]
  norm_num [Real.zero_rpow (by linarith : 2*H ≠ 0)]
  ring

private theorem coefficient_unit :
    inner ℝ (FractionalGaussianProcess.value H hH0 hH1 1)
      (FractionalGaussianProcess.value H hH0 hH1 1)=1 := by
  change inner ℝ (firstChaosEmbedding (fractionalPast H hH0 hH1))
    (firstChaosEmbedding (fractionalPast H hH0 hH1))=1
  rw [firstChaosEmbedding.inner_map_map,past_unit]

private theorem basis_pairings :
    inner ℝ (pastField H hH0 hH1) (pastField H hH0 hH1)=1 ∧
    inner ℝ (incrementField H hH0 hH1) (incrementField H hH0 hH1)=1 ∧
    inner ℝ (pastField H hH0 hH1) (incrementField H hH0 hH1)=correlation H hH0 hH1 ∧
    inner ℝ (incrementField H hH0 hH1) (pastField H hH0 hH1)=correlation H hH0 hH1 := by
  have hp : inner ℝ (pastField H hH0 hH1) (incrementField H hH0 hH1)=correlation H hH0 hH1 := by
    rw [pastField,incrementField,scalarTensor_pair_inner,coefficient_unit,one_mul]
    rfl
  refine ⟨?_,?_,hp,?_⟩
  · rw [pastField,scalarTensor_pair_inner,coefficient_unit,past_unit,one_mul]
  · rw [incrementField,scalarTensor_pair_inner,coefficient_unit,increment_unit,one_mul]
  · rw [real_inner_comm]
    exact hp

theorem correlation_eq : correlation H hH0 hH1=(2:ℝ)^(2*H)/2-1 :=
  fractional_step_covariance H hH0 hH1

theorem correlation_zero_iff : correlation H hH0 hH1=0 ↔ H=1/2 :=
  (conjugate_pairing_zero_iff (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1)).symm.trans
    (fractional_pairing_zero_iff H hH0 hH1)

/-- Actual Bochner Gaussian field pairing with the true covariance Gram matrix. -/
theorem field_pairing (a b u v : ℝ) :
    inner ℝ (field H hH0 hH1 a b) (field H hH0 hH1 u v)=
      a*u+b*v+correlation H hH0 hH1*(a*v+b*u) := by
  obtain ⟨hp,hk,hpk,hkp⟩ := basis_pairings H hH0 hH1
  simp only [field,inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,
    hp,hk,hpk,hkp]
  ring

theorem field_energy (a b : ℝ) :
    ‖field H hH0 hH1 a b‖^2=a^2+b^2+2*correlation H hH0 hH1*a*b := by
  rw [← real_inner_self_eq_norm_sq,field_pairing]
  ring

/-- The nonlocal Schur correction, as an identity in the ACTUAL field norm. -/
theorem completed_square (a b : ℝ) :
    ‖field H hH0 hH1 a b‖^2=
      (1-(correlation H hH0 hH1)^2)*a^2+(b+correlation H hH0 hH1*a)^2 := by
  rw [field_energy]
  ring

/-- These are genuine conditional expectations in the observed past of the
CONSTRUCTED continuous fractional process, at the left grid times0 and1. -/
theorem cellwise_conditioning_actual (a b : ℝ) :
    (gaussianProduct[(a • FractionalGaussianProcess.value H hH0 hH1 1) |
      ContinuousFractionalPrediction.naturalPast H hH0 hH1 0]
        =ᵐ[gaussianProduct] fun _ => (0:ℝ)) ∧
    (gaussianProduct[(b • FractionalGaussianProcess.value H hH0 hH1 1) |
      ContinuousFractionalPrediction.naturalPast H hH0 hH1 1]
        =ᵐ[gaussianProduct] (b • FractionalGaussianProcess.value H hH0 hH1 1)) := by
  have h0 : conditionalProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 0)
      (FractionalGaussianProcess.value H hH0 hH1 1)=0 := FractionalPredictionObstruction.forecast_zero H hH0 hH1
  have h1 : conditionalProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 1)
      (FractionalGaussianProcess.value H hH0 hH1 1)=FractionalGaussianProcess.value H hH0 hH1 1 :=
    (generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 1)).starProjection_eq_self_iff.mpr
      (FractionalPredictionObstruction.current_mem_generated H hH0 hH1 1)
  have ha := ContinuousFractionalPrediction.conditionalProjection_actual_past H hH0 hH1 0
    (a • FractionalGaussianProcess.value H hH0 hH1 1)
  have hb := ContinuousFractionalPrediction.conditionalProjection_actual_past H hH0 hH1 1
    (b • FractionalGaussianProcess.value H hH0 hH1 1)
  rw [map_smul,h0,smul_zero] at ha
  rw [map_smul,h1] at hb
  exact ⟨ha.symm.trans (Lp.coeFn_zero ℝ 2 gaussianProduct),
    hb.symm.trans (Lp.coeFn_smul b (FractionalGaussianProcess.value H hH0 hH1 1))⟩

/-- Cellwise conditioning gives field(0,b); its missing metric correction
has exact squared energy c_H^2 on this explicit input. -/
theorem cellwise_energy_gain :
    ‖field H hH0 hH1 0 1‖^2-‖field H hH0 hH1 (-correlation H hH0 hH1) 1‖^2=
      (correlation H hH0 hH1)^2 := by
  rw [field_energy,field_energy]
  ring

theorem cellwise_not_contractive (hH : H≠1/2) :
    ‖field H hH0 hH1 (-correlation H hH0 hH1) 1‖ < ‖field H hH0 hH1 0 1‖ := by
  have hc : correlation H hH0 hH1≠0 := fun he => hH ((correlation_zero_iff H hH0 hH1).mp he)
  have hd := cellwise_energy_gain H hH0 hH1
  nlinarith [sq_pos_of_ne_zero hc,norm_nonneg (field H hH0 hH1 (-correlation H hH0 hH1) 1),
    norm_nonneg (field H hH0 hH1 0 1)]

def adaptedGenerators : Set GaussianVectorL2 :=
  {u | ∃ A : GaussianL2, A ∈ generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 0) ∧
    u=scalarTensor (fractionalPast H hH0 hH1) A} ∪
  {u | ∃ B : GaussianL2, B ∈ generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 1) ∧
    u=scalarTensor (fractionalIncrement H hH0 hH1) B}

/-- The specified CLOSED two-cell adapted energy subspace, in the original
Gaussian vector-L2 space. No full continuous-time range identification. -/
def adaptedSpace : Submodule ℝ GaussianVectorL2 :=
  (Submodule.span ℝ (adaptedGenerators H hH0 hH1)).topologicalClosure

private theorem adapted_complete : CompleteSpace (adaptedSpace H hH0 hH1) :=
  (Submodule.span ℝ (adaptedGenerators H hH0 hH1)).isClosed_topologicalClosure.completeSpace_coe
attribute [local instance] adapted_complete

/-- Each coefficient admitted by the defining Gaussian past subspace is an
actual conditional fixed point in the observed CONTINUOUS fractional past. -/
theorem generator_coefficient_actual (t : ℝ≥0) (F : GaussianL2)
    (hF : F ∈ generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)) :
    F =ᵐ[gaussianProduct] gaussianProduct[F | ContinuousFractionalPrediction.naturalPast H hH0 hH1 t] := by
  have he : conditionalProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 t) F=F :=
    (generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 t)).starProjection_eq_self_iff.mpr hF
  simpa only [he] using ContinuousFractionalPrediction.conditionalProjection_actual_past H hH0 hH1 t F

private theorem zero_past_orthogonality (A : GaussianL2)
    (hA : A ∈ generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 0)) :
    inner ℝ (FractionalGaussianProcess.value H hH0 hH1 1) A=0 := by
  have ho := (generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 0)).starProjection_inner_eq_zero
    (FractionalGaussianProcess.value H hH0 hH1 1) A hA
  change inner ℝ (FractionalGaussianProcess.value H hH0 hH1 1-
    FractionalPredictionObstruction.forecast H hH0 hH1 0) A=0 at ho
  rw [FractionalPredictionObstruction.forecast_zero,sub_zero] at ho
  exact ho

attribute [local irreducible] pastField incrementField field

private theorem residual_generators (a b : ℝ) (u : GaussianVectorL2)
    (hu : u ∈ adaptedGenerators H hH0 hH1) :
    inner ℝ (field H hH0 hH1 a b-field H hH0 hH1 0 (b+correlation H hH0 hH1*a)) u=0 := by
  have hr : field H hH0 hH1 a b-field H hH0 hH1 0 (b+correlation H hH0 hH1*a)=
      a • (pastField H hH0 hH1-correlation H hH0 hH1 • incrementField H hH0 hH1) := by
    simp only [field,zero_smul,zero_add]
    module
  rcases hu with ⟨A,hA,rfl⟩ | ⟨B,hB,rfl⟩
  · rw [hr,real_inner_smul_left,inner_sub_left,real_inner_smul_left]
    simp only [pastField,incrementField,scalarTensor_pair_inner,
      zero_past_orthogonality H hH0 hH1 A hA,zero_mul,mul_zero,sub_self]
  · rw [hr,real_inner_smul_left,inner_sub_left,real_inner_smul_left]
    simp only [pastField,incrementField,scalarTensor_pair_inner,increment_unit,mul_one]
    change a*(inner ℝ (FractionalGaussianProcess.value H hH0 hH1 1) B*correlation H hH0 hH1-
      correlation H hH0 hH1*inner ℝ (FractionalGaussianProcess.value H hH0 hH1 1) B)=0
    ring

/-- Exact original-Hilbert orthogonal projection; the Schur correction c_H*a
is necessary on the second grid coefficient. -/
theorem adapted_projection (a b : ℝ) :
    (adaptedSpace H hH0 hH1).starProjection (field H hH0 hH1 a b)=
      field H hH0 hH1 0 (b+correlation H hH0 hH1*a) := by
  have hb : incrementField H hH0 hH1 ∈ adaptedSpace H hH0 hH1 := by
    apply (Submodule.span ℝ (adaptedGenerators H hH0 hH1)).le_topologicalClosure
    apply Submodule.subset_span
    exact Or.inr ⟨FractionalGaussianProcess.value H hH0 hH1 1,
      FractionalPredictionObstruction.current_mem_generated H hH0 hH1 1,by rw [incrementField]⟩
  have ht : field H hH0 hH1 0 (b+correlation H hH0 hH1*a) ∈ adaptedSpace H hH0 hH1 := by
    simpa only [field,zero_smul,zero_add] using
      (adaptedSpace H hH0 hH1).smul_mem (b+correlation H hH0 hH1*a) hb
  have hk : adaptedSpace H hH0 hH1 ≤
      (innerSL ℝ (field H hH0 hH1 a b-field H hH0 hH1 0 (b+correlation H hH0 hH1*a))).ker := by
    apply Submodule.topologicalClosure_minimal
    · exact Submodule.span_le.mpr (fun u hu => residual_generators H hH0 hH1 a b u hu)
    · exact (innerSL ℝ _).isClosed_ker
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero ht
  intro u hu
  exact hk hu

theorem projection_discrepancy_energy (a b : ℝ) :
    ‖(adaptedSpace H hH0 hH1).starProjection (field H hH0 hH1 a b)-field H hH0 hH1 0 b‖^2=
      (correlation H hH0 hH1*a)^2 := by
  rw [adapted_projection]
  have he : field H hH0 hH1 0 (b+correlation H hH0 hH1*a)-field H hH0 hH1 0 b=
      field H hH0 hH1 0 (correlation H hH0 hH1*a) := by
    simp only [field,zero_smul,zero_add]
    module
  rw [he,field_energy]
  ring

/-- The SAME actual covariance-square is the previously verified Gaussian
divergence correction. This is a field-norm identity, not a new integral. -/
theorem shared_divergence_correction :
    ‖field H hH0 hH1 0 1‖^2-‖field H hH0 hH1 (-correlation H hH0 hH1) 1‖^2 =
      ‖GaussianQuadraticSourceHodge.mixedTarget (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1)‖^2-
      ‖scalarTensor (fractionalIncrement H hH0 hH1) (firstChaosEmbedding (fractionalPast H hH0 hH1))‖^2 := by
  rw [cellwise_energy_gain,rank_divergence_correction]
  rfl

/-- The corrected projection is in the EXISTING full Gaussian divergence graph
on this explicit family. This is not domain preservation on all adapted fields. -/
theorem projected_divergence_graph (a b : ℝ) :
    ((adaptedSpace H hH0 hH1).starProjection (field H hH0 hH1 a b),
      (b+correlation H hH0 hH1*a) • GaussianQuadraticSourceHodge.mixedTarget
        (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1)) ∈
      hilbertDivergence.graph := by
  rw [adapted_projection]
  have hg := hilbertDivergence.graph.smul_mem
    (b+correlation H hH0 hH1*a)
    (GaussianQuadraticSourceHodge.mixed_divergence_graph
      (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1))
  simpa only [Prod.smul_mk,field,zero_smul,zero_add,incrementField,
    FractionalGaussianProcess.value,fractionalPast] using hg

/-- Even the corrected adapted projection retains the true adjoint trace term. -/
theorem projected_divergence_energy (a b : ℝ) :
    ‖(b+correlation H hH0 hH1*a) • GaussianQuadraticSourceHodge.mixedTarget
      (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1)‖^2-
      ‖(adaptedSpace H hH0 hH1).starProjection (field H hH0 hH1 a b)‖^2 =
        (b+correlation H hH0 hH1*a)^2*(correlation H hH0 hH1)^2 := by
  have hc := rank_divergence_correction (fractionalPast H hH0 hH1)
    (fractionalIncrement H hH0 hH1)
  have hu : ‖scalarTensor (fractionalIncrement H hH0 hH1)
      (firstChaosEmbedding (fractionalPast H hH0 hH1))‖^2=1 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [incrementField,FractionalGaussianProcess.value,fractionalPast] using
      (basis_pairings H hH0 hH1).2.1
  rw [hu] at hc
  change _-1=(correlation H hH0 hH1)^2 at hc
  rw [adapted_projection,field_energy,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  rw [sub_eq_iff_eq_add] at hc
  rw [hc]
  ring
end OperatorDerivativeRewrite.Foundation.FractionalGridProjection
