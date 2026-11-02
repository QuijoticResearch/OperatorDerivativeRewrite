import Foundation.FractionalGridProjection
import Foundation.GaussianConditionalCompactness

/-! A concrete test of the adapted derivative/adjoint identity, using the
actual fractional Gaussian source, full observed past and existing graphs.
Only the specified closed two-cell adapted subspace is identified here. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FractionalAdaptedAdjointObstruction
open InfiniteGaussian GaussianTimeSpaceHermite GaussianTimeFieldNorm
open StochasticCauchyFractionalDivergence GaussianConditionalGraph FractionalGridProjection
variable (H : ℝ) (hH0 : 0<H) (hH1 : H<1)

local instance : CompleteSpace (adaptedSpace H hH0 hH1) :=
  (Submodule.span ℝ (adaptedGenerators H hH0 hH1)).isClosed_topologicalClosure.completeSpace_coe

def incrementValue : GaussianL2 := firstChaosEmbedding (fractionalIncrement H hH0 hH1)
def incrementPrediction : GaussianL2 :=
  conditionalProjection (FractionalPredictionObstruction.pastDirections H hH0 hH1 1)
    (incrementValue H hH0 hH1)
def extraField : GaussianVectorL2 := scalarTensor (fractionalPast H hH0 hH1) (incrementValue H hH0 hH1)
def derivativeField : GaussianVectorL2 := incrementField H hH0 hH1+extraField H hH0 hH1
def defectField : GaussianVectorL2 := correlation H hH0 hH1 •
  scalarTensor (fractionalIncrement H hH0 hH1) (incrementPrediction H hH0 hH1)

private theorem past_unit : inner ℝ (fractionalPast H hH0 hH1) (fractionalPast H hH0 hH1)=1 := by
  simp only [fractionalPast,FractionalWickCovariance.direction_inner,FractionalSpectralGeometry.covariance]
  norm_num [Real.zero_rpow (by linarith : 2*H≠0)]

private theorem increment_unit :
    inner ℝ (fractionalIncrement H hH0 hH1) (fractionalIncrement H hH0 hH1)=1 := by
  simp only [fractionalIncrement,fractionalPast,inner_sub_left,inner_sub_right,
    FractionalWickCovariance.direction_inner,FractionalSpectralGeometry.covariance]
  norm_num [Real.zero_rpow (by linarith : 2*H≠0)]
  ring

theorem input_adapted : incrementField H hH0 hH1 ∈ adaptedSpace H hH0 hH1 := by
  apply (Submodule.span ℝ (adaptedGenerators H hH0 hH1)).le_topologicalClosure
  apply Submodule.subset_span
  exact Or.inr ⟨FractionalGaussianProcess.value H hH0 hH1 1,
    FractionalPredictionObstruction.current_mem_generated H hH0 hH1 1,rfl⟩

theorem input_unit : ‖incrementField H hH0 hH1‖^2=1 := by
  rw [← real_inner_self_eq_norm_sq,incrementField,scalarTensor_pair_inner]
  change inner ℝ (firstChaosEmbedding (fractionalPast H hH0 hH1))
    (firstChaosEmbedding (fractionalPast H hH0 hH1))*_=1
  rw [firstChaosEmbedding.inner_map_map,past_unit,increment_unit,one_mul]

theorem input_divergence_graph :
    (incrementField H hH0 hH1,GaussianQuadraticSourceHodge.mixedTarget
      (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1)) ∈ hilbertDivergence.graph :=
  GaussianQuadraticSourceHodge.mixed_divergence_graph _ _

theorem output_derivative_graph :
    (GaussianQuadraticSourceHodge.mixedTarget
      (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1),
      derivativeField H hH0 hH1) ∈ closedCylindricalDerivative.graph :=
  GaussianQuadraticSourceHodge.mixed_derivative_graph _ _

theorem extra_pairing : inner ℝ (extraField H hH0 hH1) (incrementField H hH0 hH1)=
    (correlation H hH0 hH1)^2 := by
  rw [extraField,incrementField,scalarTensor_pair_inner]
  change inner ℝ (firstChaosEmbedding (fractionalIncrement H hH0 hH1))
    (firstChaosEmbedding (fractionalPast H hH0 hH1))*_= _
  rw [firstChaosEmbedding.inner_map_map]
  have hk : inner ℝ (fractionalIncrement H hH0 hH1) (fractionalPast H hH0 hH1)=
      correlation H hH0 hH1 := real_inner_comm _ _
  rw [hk]
  change correlation H hH0 hH1*correlation H hH0 hH1=(correlation H hH0 hH1)^2
  ring

theorem projected_defect_pairing :
    inner ℝ ((adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1)-
      incrementField H hH0 hH1) (incrementField H hH0 hH1)=(correlation H hH0 hH1)^2 := by
  have ho := (adaptedSpace H hH0 hH1).starProjection_inner_eq_zero
    (derivativeField H hH0 hH1) (incrementField H hH0 hH1) (input_adapted H hH0 hH1)
  rw [inner_sub_left,derivativeField,inner_add_left] at ho
  rw [inner_sub_left,derivativeField]
  have he := extra_pairing H hH0 hH1
  linarith

theorem projected_defect_norm_lower :
    (correlation H hH0 hH1)^2 ≤
      ‖(adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1)-incrementField H hH0 hH1‖ := by
  have hu : ‖incrementField H hH0 hH1‖=1 := by
    have hh := input_unit H hH0 hH1
    nlinarith [norm_nonneg (incrementField H hH0 hH1)]
  have hc := real_inner_le_norm
    ((adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1)-incrementField H hH0 hH1)
    (incrementField H hH0 hH1)
  rwa [projected_defect_pairing,hu,mul_one] at hc

theorem adapted_derivative_not_identity (hH : H≠1/2) :
    (adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1) ≠ incrementField H hH0 hH1 := by
  intro he
  have hp := projected_defect_pairing H hH0 hH1
  rw [he,sub_self,inner_zero_left] at hp
  exact hH ((correlation_zero_iff H hH0 hH1).mp (sq_eq_zero_iff.mp hp.symm))

private theorem zero_past_orthogonality (F A : GaussianL2)
    (hc : inner ℝ F gaussianOne=0)
    (hA : A ∈ generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 0)) :
    inner ℝ F A=0 := by
  have hker : generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 0) ≤
      (innerSL ℝ F).ker := by
    rw [generated,← familyPolynomial_closure]
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨p,rfl⟩
      change inner ℝ F (familyPolynomialEmbedding _ p)=0
      rw [FractionalPredictionObstruction.zero_past_polynomial_constant,real_inner_smul_right,hc,mul_zero]
    · exact (innerSL ℝ F).isClosed_ker
  exact hker hA

private theorem increment_centered : inner ℝ (incrementValue H hH0 hH1) gaussianOne=0 := by
  rw [real_inner_comm,gaussianOne_inner_eq_integral]
  exact firstChaos_integral _

private theorem one_past : gaussianOne ∈ generated
    (FractionalPredictionObstruction.pastDirections H hH0 hH1 1) := by
  have hm := GaussianWickConditionalProjection.wick_mem_generated_of_sourceSpan
    (FractionalPredictionObstruction.pastDirections H hH0 hH1 1) 0
    (GaussianWickConditionalProjection.sourceSpan _).zero_mem 0
  simpa only [GaussianTimeSpaceHermite.wick,GaussianTimeSpaceHermite.core_zero] using hm

private theorem prediction_centered : inner ℝ (incrementPrediction H hH0 hH1) gaussianOne=0 := by
  have ho := (generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 1)).starProjection_inner_eq_zero
    (incrementValue H hH0 hH1) gaussianOne (one_past H hH0 hH1)
  change inner ℝ (incrementValue H hH0 hH1-incrementPrediction H hH0 hH1) gaussianOne=0 at ho
  rw [inner_sub_left,increment_centered] at ho
  linarith

theorem prediction_actual : incrementPrediction H hH0 hH1 =ᵐ[gaussianProduct]
    gaussianProduct[incrementValue H hH0 hH1 | ContinuousFractionalPrediction.naturalPast H hH0 hH1 1] :=
  ContinuousFractionalPrediction.conditionalProjection_actual_past H hH0 hH1 1 _

private theorem extra_residual_generators (u : GaussianVectorL2)
    (hu : u ∈ adaptedGenerators H hH0 hH1) :
    inner ℝ (extraField H hH0 hH1-defectField H hH0 hH1) u=0 := by
  rcases hu with ⟨A,hA,rfl⟩ | ⟨B,hB,rfl⟩
  · rw [inner_sub_left,extraField,defectField,real_inner_smul_left]
    simp only [scalarTensor_pair_inner,
      zero_past_orthogonality H hH0 hH1 _ _ (increment_centered H hH0 hH1) hA,
      zero_past_orthogonality H hH0 hH1 _ _ (prediction_centered H hH0 hH1) hA,
      zero_mul,mul_zero,sub_self]
  · have ho := (generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 1)).starProjection_inner_eq_zero
      (incrementValue H hH0 hH1) B hB
    change inner ℝ (incrementValue H hH0 hH1-incrementPrediction H hH0 hH1) B=0 at ho
    rw [inner_sub_left] at ho
    rw [inner_sub_left,extraField,defectField,real_inner_smul_left]
    simp only [scalarTensor_pair_inner,increment_unit,mul_one]
    change inner ℝ (incrementValue H hH0 hH1) B*correlation H hH0 hH1-
      correlation H hH0 hH1*inner ℝ (incrementPrediction H hH0 hH1) B=0
    rw [sub_eq_zero.mp ho]
    ring

theorem extra_projection : (adaptedSpace H hH0 hH1).starProjection (extraField H hH0 hH1)=
    defectField H hH0 hH1 := by
  have hm : scalarTensor (fractionalIncrement H hH0 hH1) (incrementPrediction H hH0 hH1) ∈
      adaptedSpace H hH0 hH1 := by
    apply (Submodule.span ℝ (adaptedGenerators H hH0 hH1)).le_topologicalClosure
    apply Submodule.subset_span
    exact Or.inr ⟨incrementPrediction H hH0 hH1,
      (generated _).starProjection_apply_mem (incrementValue H hH0 hH1),rfl⟩
  have ht : defectField H hH0 hH1 ∈ adaptedSpace H hH0 hH1 :=
    (adaptedSpace H hH0 hH1).smul_mem _ hm
  have hk : adaptedSpace H hH0 hH1 ≤
      (innerSL ℝ (extraField H hH0 hH1-defectField H hH0 hH1)).ker := by
    apply Submodule.topologicalClosure_minimal
    · exact Submodule.span_le.mpr (fun u hu => extra_residual_generators H hH0 hH1 u hu)
    · exact (innerSL ℝ _).isClosed_ker
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero ht
  intro u hu
  exact hk hu

theorem projected_derivative_exact :
    (adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1)=
      incrementField H hH0 hH1+defectField H hH0 hH1 := by
  rw [derivativeField,map_add,extra_projection,
    (adaptedSpace H hH0 hH1).starProjection_eq_self_iff.mpr (input_adapted H hH0 hH1)]

theorem brownian_identity (hH : H=1/2) :
    (adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1)=incrementField H hH0 hH1 := by
  rw [projected_derivative_exact,defectField,(correlation_zero_iff H hH0 hH1).mpr hH,zero_smul,add_zero]

/-- Exact threshold for the proposed adapted derivative/adjoint identity on
this genuine second-chaos example. No continuous-time range identification. -/
theorem identity_iff :
    (adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1)=
      incrementField H hH0 hH1 ↔ H=1/2 := by
  constructor
  · intro he
    by_contra hH
    exact adapted_derivative_not_identity H hH0 hH1 hH he
  · exact brownian_identity H hH0 hH1

/-- The full-past forecast is tested against an actual past coordinate;
it is not replaced by projection onto that single coordinate. -/
theorem prediction_pairing :
    inner ℝ (incrementPrediction H hH0 hH1) (FractionalGaussianProcess.value H hH0 hH1 1)=
      correlation H hH0 hH1 := by
  have ho := (generated (FractionalPredictionObstruction.pastDirections H hH0 hH1 1)).starProjection_inner_eq_zero
    (incrementValue H hH0 hH1) (FractionalGaussianProcess.value H hH0 hH1 1)
    (FractionalPredictionObstruction.current_mem_generated H hH0 hH1 1)
  change inner ℝ (incrementValue H hH0 hH1-incrementPrediction H hH0 hH1)
    (FractionalGaussianProcess.value H hH0 hH1 1)=0 at ho
  rw [inner_sub_left] at ho
  have hi : inner ℝ (incrementValue H hH0 hH1) (FractionalGaussianProcess.value H hH0 hH1 1)=
      correlation H hH0 hH1 := by
    change inner ℝ (firstChaosEmbedding (fractionalIncrement H hH0 hH1))
      (firstChaosEmbedding (fractionalPast H hH0 hH1))= _
    rw [firstChaosEmbedding.inner_map_map]
    exact real_inner_comm _ _
  linarith

/-- Exact energy of the remaining term, with the ACTUAL full-past forecast. -/
theorem projected_defect_energy :
    ‖(adaptedSpace H hH0 hH1).starProjection (derivativeField H hH0 hH1)-incrementField H hH0 hH1‖^2=
      (correlation H hH0 hH1)^2*‖incrementPrediction H hH0 hH1‖^2 := by
  rw [projected_derivative_exact,add_sub_cancel_left,defectField,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs]
  rw [← real_inner_self_eq_norm_sq (x := scalarTensor (fractionalIncrement H hH0 hH1)
    (incrementPrediction H hH0 hH1)),scalarTensor_pair_inner,increment_unit,mul_one,
    real_inner_self_eq_norm_sq]
/-- The scalar obstruction is independent of which orthogonally projected
subspace is proposed: inclusion of the genuine input field already suffices. -/
theorem arbitrary_projection_defect_pairing (K : Submodule ℝ GaussianVectorL2)
    [K.HasOrthogonalProjection] (hu : incrementField H hH0 hH1 ∈ K) :
    inner ℝ (K.starProjection (derivativeField H hH0 hH1)-incrementField H hH0 hH1)
      (incrementField H hH0 hH1)=(correlation H hH0 hH1)^2 := by
  have ho := K.starProjection_inner_eq_zero (derivativeField H hH0 hH1)
    (incrementField H hH0 hH1) hu
  rw [inner_sub_left,derivativeField,inner_add_left] at ho
  rw [inner_sub_left,derivativeField]
  have he := extra_pairing H hH0 hH1
  linarith

/-- Even a different closed adapted space cannot make the projected
derivative a left inverse of the actual divergence on this input. -/
theorem no_orthogonal_right_inverse (K : Submodule ℝ GaussianVectorL2)
    [K.HasOrthogonalProjection] (hu : incrementField H hH0 hH1 ∈ K) (hH : H≠1/2) :
    K.starProjection (derivativeField H hH0 hH1) ≠ incrementField H hH0 hH1 := by
  intro he
  have hp := arbitrary_projection_defect_pairing H hH0 hH1 K hu
  rw [he,sub_self,inner_zero_left] at hp
  exact hH ((correlation_zero_iff H hH0 hH1).mp (sq_eq_zero_iff.mp hp.symm))

/-- The target is genuinely centered, so mean subtraction cannot repair
the following reconstruction obstruction. -/
theorem output_centered :
    (∫ w,GaussianQuadraticSourceHodge.mixedTarget (fractionalIncrement H hH0 hH1)
      (fractionalPast H hH0 hH1) w ∂gaussianProduct)=0 := by
  have hc := (GaussianDivergenceRecovery.exists_divergence_iff_centered
    (GaussianQuadraticSourceHodge.mixedTarget (fractionalIncrement H hH0 hH1)
      (fractionalPast H hH0 hH1))).mp ⟨_,input_divergence_graph H hH0 hH1⟩
  rwa [gaussianOne_inner_eq_integral] at hc

/-- No orthogonal adapted-space repair containing the genuine step input
can reconstruct this centered observable by the EXISTING divergence adjoint. -/
theorem no_orthogonal_reconstruction (K : Submodule ℝ GaussianVectorL2)
    [K.HasOrthogonalProjection] (hu : incrementField H hH0 hH1 ∈ K) (hH : H≠1/2) :
    (K.starProjection (derivativeField H hH0 hH1),
      GaussianQuadraticSourceHodge.mixedTarget (fractionalIncrement H hH0 hH1)
        (fractionalPast H hH0 hH1)) ∉ hilbertDivergence.graph := by
  intro hg
  have hd := GaussianNumberSectors.graph_duality (output_derivative_graph H hH0 hH1) hg
  rw [real_inner_self_eq_norm_sq] at hd
  have ho := K.starProjection_inner_eq_zero (derivativeField H hH0 hH1)
    (K.starProjection (derivativeField H hH0 hH1)) (K.starProjection_apply_mem _)
  rw [inner_sub_left,real_inner_self_eq_norm_sq] at ho
  have hn : ‖K.starProjection (derivativeField H hH0 hH1)‖^2=
      ‖GaussianQuadraticSourceHodge.mixedTarget (fractionalIncrement H hH0 hH1)
        (fractionalPast H hH0 hH1)‖^2 := by linarith
  have hp := arbitrary_projection_defect_pairing H hH0 hH1 K hu
  rw [inner_sub_left,real_inner_self_eq_norm_sq,input_unit] at hp
  have hpu : inner ℝ (K.starProjection (derivativeField H hH0 hH1))
      (incrementField H hH0 hH1)=1+(correlation H hH0 hH1)^2 := by linarith
  have hb := real_inner_mul_inner_self_le (K.starProjection (derivativeField H hH0 hH1))
    (incrementField H hH0 hH1)
  rw [hpu,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,input_unit,mul_one,hn] at hb
  have hf := rank_divergence_correction (fractionalPast H hH0 hH1) (fractionalIncrement H hH0 hH1)
  change ‖GaussianQuadraticSourceHodge.mixedTarget (fractionalIncrement H hH0 hH1)
      (fractionalPast H hH0 hH1)‖^2-‖incrementField H hH0 hH1‖^2=(correlation H hH0 hH1)^2 at hf
  rw [input_unit] at hf
  have hc : correlation H hH0 hH1≠0 := fun he => hH ((correlation_zero_iff H hH0 hH1).mp he)
  nlinarith [sq_pos_of_ne_zero hc,sq_nonneg ((correlation H hH0 hH1)^2)]

end OperatorDerivativeRewrite.Foundation.FractionalAdaptedAdjointObstruction
