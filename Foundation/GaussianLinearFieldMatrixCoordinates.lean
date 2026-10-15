import Foundation.GaussianLinearFieldTranspose
import Foundation.GaussianRecoveryCompactnessObstruction

/-! Explicit square-summable matrix coordinates for completed linear Gaussian fields. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianLinearFieldMatrixCoordinates
open GaussianTimeFieldNorm InfiniteGaussian GaussianLinearFieldDivergenceCompletion GaussianLinearFieldTranspose
open GaussianJointRecoveryIntertwining

def unit (n : ℕ) : CoefficientSpace := lp.single 2 n (1 : ℝ)
def matrixUnit (p : ℕ × ℕ) : GaussianVectorL2 := scalarTensor (unit p.1) (firstChaosEmbedding (unit p.2))

theorem units_orthonormal : Orthonormal ℝ unit := GaussianRecoveryCompactnessObstruction.coefficient_single_orthonormal

theorem matrixUnits_orthonormal : Orthonormal ℝ matrixUnit := by
  rw [orthonormal_iff_ite]
  intro p q
  rw [matrixUnit,matrixUnit,scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map]
  have h := units_orthonormal
  rw [orthonormal_iff_ite] at h
  rw [h,h]
  by_cases hi : p.1=q.1 <;> by_cases hj : p.2=q.2 <;> simp [hi,hj,Prod.ext_iff]

def matrixSynthesis : lp (fun _ : ℕ × ℕ => ℝ) 2 →ₗᵢ[ℝ] GaussianVectorL2 :=
  matrixUnits_orthonormal.orthogonalFamily.linearIsometry

theorem matrixSynthesis_single (p : ℕ × ℕ) : matrixSynthesis (lp.single 2 p (1 : ℝ))=matrixUnit p := by
  simpa only [matrixSynthesis,LinearIsometry.toSpanSingleton_apply,one_smul] using
    matrixUnits_orthonormal.orthogonalFamily.linearIsometry_apply_single (1 : ℝ) (i := p)

theorem coefficient_hasSum (u : CoefficientSpace) : HasSum (fun n => u n • unit n) u := by
  have he (n : ℕ) : u n • unit n=lp.single 2 n (u n) := by
    simp only [unit,← lp.single_smul,smul_eq_mul,mul_one]
  simpa only [he] using lp.hasSum_single (by norm_num : (2 : ℝ≥0∞)≠⊤) u

theorem matrixSynthesis_range : matrixSynthesis.toLinearMap.range=linearGaussianFields := by
  have hc : IsClosed (matrixSynthesis.toLinearMap.range : Set GaussianVectorL2) :=
    HilbertRepresentation.isClosed_isometry_range matrixSynthesis
  have hm (i j : ℕ) : matrixUnit (i,j)∈matrixSynthesis.toLinearMap.range :=
    ⟨lp.single 2 (i,j) 1,matrixSynthesis_single (i,j)⟩
  have hr (u : CoefficientSpace) (j : ℕ) : scalarTensor u (firstChaosEmbedding (unit j))∈matrixSynthesis.toLinearMap.range := by
    have hs := (sourceTensor (firstChaosEmbedding (unit j))).hasSum (coefficient_hasSum u)
    apply hc.mem_of_tendsto hs
    exact Eventually.of_forall fun s => matrixSynthesis.toLinearMap.range.sum_mem
      (fun i hi => by
        rw [map_smul]
        exact matrixSynthesis.toLinearMap.range.smul_mem (u i) (hm i j))
  have hall (u v : CoefficientSpace) : scalarTensor u (firstChaosEmbedding v)∈matrixSynthesis.toLinearMap.range := by
    have hs := (scalarTensor u).hasSum (firstChaosEmbedding.toContinuousLinearMap.hasSum (coefficient_hasSum v))
    apply hc.mem_of_tendsto hs
    exact Eventually.of_forall fun s => matrixSynthesis.toLinearMap.range.sum_mem
      (fun j hj => by
        rw [map_smul,map_smul]
        exact matrixSynthesis.toLinearMap.range.smul_mem (v j) (hr u j))
  apply le_antisymm
  · rintro w ⟨c,rfl⟩
    apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
      (matrixUnits_orthonormal.orthogonalFamily.hasSum_linearIsometry c)
    exact Eventually.of_forall fun s => linearGaussianFields.sum_mem
      (fun p hp => linearGaussianFields.smul_mem (c p) (linear_rank_mem (unit p.1) (unit p.2)))
  · apply linearFieldCore.topologicalClosure_minimal _ hc
    apply Submodule.span_le.mpr
    rintro _ ⟨u,v,rfl⟩
    exact hall u v

def matrixIntoFields : lp (fun _ : ℕ × ℕ => ℝ) 2 →ₗᵢ[ℝ] linearGaussianFields where
  toLinearMap := matrixSynthesis.toLinearMap.codRestrict linearGaussianFields
    (fun c => matrixSynthesis_range ▸ LinearMap.mem_range_self matrixSynthesis.toLinearMap c)
  norm_map' c := matrixSynthesis.norm_map c

theorem matrixIntoFields_surjective : Function.Surjective matrixIntoFields := by
  intro v
  have hm : (v : GaussianVectorL2)∈matrixSynthesis.toLinearMap.range := matrixSynthesis_range.symm ▸ v.property
  obtain ⟨c,hc⟩ := hm
  exact ⟨c,Subtype.ext hc⟩

def matrixUnitary : lp (fun _ : ℕ × ℕ => ℝ) 2 ≃ₗᵢ[ℝ] linearGaussianFields :=
  LinearIsometryEquiv.ofSurjective matrixIntoFields matrixIntoFields_surjective

def coordinates (v : linearGaussianFields) : lp (fun _ : ℕ × ℕ => ℝ) 2 := matrixUnitary.symm v

theorem coordinates_norm (v : linearGaussianFields) : ‖coordinates v‖=‖v‖ := matrixUnitary.symm.norm_map v

theorem coordinates_apply (v : linearGaussianFields) (p : ℕ × ℕ) :
    coordinates v p=inner ℝ (matrixUnit p) (v : GaussianVectorL2) := by
  have h := matrixUnitary.inner_map_map (lp.single 2 p (1 : ℝ)) (matrixUnitary.symm v)
  rw [matrixUnitary.apply_symm_apply] at h
  change inner ℝ (matrixSynthesis (lp.single 2 p (1 : ℝ))) (v : GaussianVectorL2)=
    inner ℝ (lp.single 2 p (1 : ℝ)) (coordinates v) at h
  rw [matrixSynthesis_single,lp.inner_single_left] at h
  simpa only [Real.inner_apply,one_mul] using h.symm

theorem coordinates_transpose (v : linearGaussianFields) (i j : ℕ) :
    coordinates ⟨transpose v,transpose_mem v.property⟩ (i,j)=coordinates v (j,i) := by
  rw [coordinates_apply,coordinates_apply]
  exact transpose_matrix_coefficient (unit i) (unit j) v

theorem coordinates_energy (v : linearGaussianFields) :
    HasSum (fun p => (coordinates v p)^2) (‖(v : GaussianVectorL2)‖^2) := by
  change HasSum (fun p => (coordinates v p)^2) (‖v‖^2)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,sq_abs,coordinates_norm] using
    lp.hasSum_norm (by norm_num : 0<(2 : ℝ≥0∞).toReal) (coordinates v)

theorem gradient_mem {v : GaussianVectorL2} (hv : v∈linearGaussianFields) :
    GaussianSourceHodge.gradientProjection v∈linearGaussianFields := by
  rw [← symmetricPart_eq]
  exact linearGaussianFields.smul_mem _ (linearGaussianFields.add_mem hv (transpose_mem hv))

theorem coordinates_gradient (v : linearGaussianFields) (i j : ℕ) :
    coordinates ⟨GaussianSourceHodge.gradientProjection v,gradient_mem v.property⟩ (i,j)=
      (coordinates v (i,j)+coordinates v (j,i))/2 := by
  rw [coordinates_apply]
  change inner ℝ (matrixUnit (i,j)) (GaussianSourceHodge.gradientProjection (v : GaussianVectorL2))=_
  rw [← symmetricPart_eq,real_inner_smul_right,inner_add_right]
  change (1/2 : ℝ)*(inner ℝ (matrixUnit (i,j)) (v : GaussianVectorL2)+
    inner ℝ (matrixUnit (i,j)) (transpose v))=_
  have ht := transpose_matrix_coefficient (unit i) (unit j) (v : GaussianVectorL2)
  change inner ℝ (matrixUnit (i,j)) (transpose v)=inner ℝ (matrixUnit (j,i)) (v : GaussianVectorL2) at ht
  rw [ht,coordinates_apply,coordinates_apply]
  ring

theorem divergence_matrix_energy (v : linearGaussianFields) :
    HasSum (fun p : ℕ × ℕ => 2*((coordinates v p+coordinates v (p.2,p.1))/2)^2)
      (‖completedDivergence v‖^2) := by
  have hs := (coordinates_energy ⟨GaussianSourceHodge.gradientProjection v,gradient_mem v.property⟩).mul_left 2
  have he (p : ℕ × ℕ) := coordinates_gradient v p.1 p.2
  simpa only [Prod.mk.eta,he,completed_energy v.property] using hs

theorem coordinates_injective {v w : linearGaussianFields} (h : coordinates v=coordinates w) : v=w :=
  matrixUnitary.symm.injective h

theorem divergence_zero_iff_skew_coordinates (v : linearGaussianFields) :
    completedDivergence v=0 ↔ ∀ i j,coordinates v (i,j)=-coordinates v (j,i) := by
  rw [completed_kernel_antisymmetric v.property]
  constructor
  · intro ht i j
    have h := coordinates_transpose v j i
    rw [coordinates_apply] at h
    change inner ℝ (matrixUnit (j,i)) (transpose (v : GaussianVectorL2))=coordinates v (i,j) at h
    rw [ht,inner_neg_right,← coordinates_apply] at h
    exact h.symm
  · intro h
    have he : (⟨transpose v,transpose_mem v.property⟩ : linearGaussianFields)=-v := by
      apply coordinates_injective
      apply lp.ext
      funext p
      rw [coordinates_transpose,coordinates_apply (-v) p]
      change coordinates v (p.2,p.1)=inner ℝ (matrixUnit p) (-(v : GaussianVectorL2))
      rw [inner_neg_right,← coordinates_apply]
      exact h p.2 p.1
    exact congrArg Subtype.val he

end OperatorDerivativeRewrite.Foundation.GaussianLinearFieldMatrixCoordinates




