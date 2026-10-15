import Foundation.GaussianLinearFieldMatrixCoordinates
import Foundation.GaussianChaosLowering
import Foundation.GaussianConditionalFullGraphs

/-! Full Gaussian second-chaos recovery lies in completed linear fields; divergence is onto. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticRecoverySurjectivity
open InfiniteGaussian GaussianNumberSectors GaussianChaosLowering GaussianDivergenceRecovery
open GaussianLinearFieldDivergenceCompletion GaussianSourceHodge GaussianQuadraticSourceHodge
open GaussianRecoveryCompactnessObstruction GaussianFirstChaosRecovery
local instance : CompleteSpace linearGaussianFields :=
  (Submodule.isClosed_topologicalClosure linearFieldCore).completeSpace_coe

def vacuumProjection : GaussianVectorL2 →L[ℝ] GaussianVectorL2 :=
  vacuumEmbedding.toContinuousLinearMap.comp vacuumEmbedding.toContinuousLinearMap.adjoint

theorem component_vacuumProjection (k : CoefficientSpace) (v : GaussianVectorL2) :
    component k (vacuumProjection v)=projection 0 (component k v) := by
  change component k (vacuumEmbedding (vacuumEmbedding.toContinuousLinearMap.adjoint v))=_
  rw [vacuumEmbedding_apply,component_scalarTensor,projection_zero]
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (vacuumEmbedding k) v=_
  rw [vacuumEmbedding_apply,scalarTensor_inner]
  rfl

theorem constant_components_vacuum {v : GaussianVectorL2} (hv : ∀ k,component k v∈sector 0) :
    ∃ h : CoefficientSpace,v=scalarTensor h gaussianOne := by
  have he : v=vacuumProjection v := by
    apply sub_eq_zero.mp
    apply eq_zero_of_cylindricalVector_orthogonal
    intro f k
    rw [scalarTensor_inner]
    change inner ℝ (f : GaussianL2) (component k (v-vacuumProjection v))=0
    rw [map_sub,component_vacuumProjection,projection_fix 0 ⟨_,hv k⟩,sub_self,inner_zero_right]
  exact ⟨vacuumEmbedding.toContinuousLinearMap.adjoint v,he.trans (vacuumEmbedding_apply _)⟩

theorem sector_one_iff_firstChaos (f : GaussianL2) :
    f∈sector 1 ↔ f∈firstChaosEmbedding.toLinearMap.range := by
  constructor
  · intro hf
    let g := projectedGradient 1 f
    have hv (k : CoefficientSpace) : component k g∈sector 0 := by
      simpa only [Nat.reduceSub] using component_projectedGradient_mem 1 k f
    obtain ⟨h,hh⟩ := constant_components_vacuum hv
    have hd : (projectedGradient 1 f,(1 : ℝ) • projection 1 f)∈hilbertDivergence.graph :=
      by simpa only [Nat.cast_one] using ((mem_sectorGraph 1 _ _).mp (projectedGradient_graph 1 f)).2
    rw [projection_fix 1 ⟨_,hf⟩] at hd
    change (g,(1 : ℝ) • f)∈hilbertDivergence.graph at hd
    rw [one_smul,hh] at hd
    refine ⟨h,?_⟩
    change firstChaosEmbedding h=f
    exact hilbertDivergence.mem_graph_snd_inj (firstChaos_divergence_graph h) hd rfl
  · rintro ⟨h,rfl⟩
    change firstChaosEmbedding h∈sector 1
    apply (mem_sector 1 _).mpr
    exact ⟨scalarTensor h gaussianOne,firstChaos_derivative_graph h,
      by simpa only [Nat.cast_one,one_smul] using firstChaos_divergence_graph h⟩

theorem component_linear_mem {v : GaussianVectorL2} (hv : v∈linearGaussianFields) (k : CoefficientSpace) :
    component k v∈firstChaosEmbedding.toLinearMap.range := by
  have hs : linearFieldCore≤firstChaosEmbedding.toLinearMap.range.comap (component k).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a,b,rfl⟩
    change component k (scalarTensor a (firstChaosEmbedding b))∈firstChaosEmbedding.toLinearMap.range
    rw [component_scalarTensor]
    exact firstChaosEmbedding.toLinearMap.range.smul_mem _ ⟨b,rfl⟩
  exact (linearFieldCore.topologicalClosure_minimal hs
    ((HilbertRepresentation.isClosed_isometry_range firstChaosEmbedding).preimage (component k).continuous)) hv

theorem linear_fields_iff_components (v : GaussianVectorL2) :
    v∈linearGaussianFields ↔ ∀ k,component k v∈firstChaosEmbedding.toLinearMap.range := by
  constructor
  · exact fun hv k => component_linear_mem hv k
  · intro hv
    let p := linearGaussianFields.starProjection v
    have hp : p∈linearGaussianFields := linearGaussianFields.starProjection_apply_mem v
    have hz (k : CoefficientSpace) : component k (v-p)=0 := by
      have hm := firstChaosEmbedding.toLinearMap.range.sub_mem (hv k) (component_linear_mem hp k)
      rw [← map_sub] at hm
      obtain ⟨a,ha⟩ := hm
      have hi := linearGaussianFields.starProjection_inner_eq_zero v
        (scalarTensor k (firstChaosEmbedding a)) (linear_rank_mem k a)
      change inner ℝ (v-p) (scalarTensor k (firstChaosEmbedding a))=0 at hi
      have hj : inner ℝ (scalarTensor k (firstChaosEmbedding a)) (v-p)=0 := (real_inner_comm _ _).trans hi
      rw [scalarTensor_inner] at hj
      change inner ℝ (firstChaosEmbedding a) (component k (v-p))=0 at hj
      change firstChaosEmbedding a=component k (v-p) at ha
      rw [ha] at hj
      exact inner_self_eq_zero.mp hj
    have he : v=p := sub_eq_zero.mp (eq_zero_of_cylindricalVector_orthogonal (v-p) (fun f k => by
      rw [scalarTensor_inner]
      change inner ℝ (f : GaussianL2) (component k (v-p))=0
      rw [hz k,inner_zero_right]))
    exact he.symm ▸ hp

theorem recovery_second_chaos_linear {f : GaussianL2} (hf : f∈sector 2) : recovery f∈linearGaussianFields := by
  have hm : projectedGradient 2 f∈linearGaussianFields := by
    apply (linear_fields_iff_components _).mpr
    intro k
    apply (sector_one_iff_firstChaos _).mp
    simpa only [Nat.reduceSub] using component_projectedGradient_mem 2 k f
  have he := GaussianConditionalFullGraphs.projectedGradient_eq_number_recovery 2 f
  rw [projection_fix 2 ⟨_,hf⟩] at he
  have hh : recovery f=(1/2 : ℝ) • projectedGradient 2 f := by rw [he,smul_smul]; norm_num
  rw [hh]
  exact linearGaussianFields.smul_mem _ hm

theorem completed_divergence_recovery {f : GaussianL2} (hf : f∈sector 2) : completedDivergence (recovery f)=f := by
  have h := full_divergence_graph (recovery_second_chaos_linear hf)
  have hr := recovery_graph f
  have hz : projection 0 f=0 := by
    simpa only [show (0 : ℕ)≠2 by norm_num,ite_false] using projection_of_sector (n := 0) ⟨f,hf⟩
  rw [hz,sub_zero] at hr
  exact hilbertDivergence.mem_graph_snd_inj h hr rfl

theorem completed_divergence_onto_second_chaos (f : sector 2) :
    ∃ v : linearGaussianFields, completedDivergence v=f :=
  ⟨⟨recovery f,recovery_second_chaos_linear f.property⟩,completed_divergence_recovery f.property⟩

theorem second_recovery_energy {f : GaussianL2} (hf : f∈sector 2) : ‖recovery f‖^2=(1/2 : ℝ)*‖f‖^2 := by
  have h := completed_energy (recovery_second_chaos_linear hf)
  have hp : gradientProjection (recovery f)=recovery f :=
    gradientRange.starProjection_eq_self_iff.mpr (recovery_mem_gradientRange f)
  rw [completed_divergence_recovery hf,hp] at h
  linarith

def symmetricFields : Submodule ℝ GaussianVectorL2 := linearGaussianFields ⊓ gradientRange

def quadraticLift : sector 2 →ₗᵢ[ℝ] symmetricFields where
  toLinearMap :=
    { toFun f := ⟨Real.sqrt 2 • recovery f,
        linearGaussianFields.smul_mem _ (recovery_second_chaos_linear f.property),
        gradientRange.smul_mem _ (recovery_mem_gradientRange f)⟩
      map_add' f g := by
        apply Subtype.ext
        change Real.sqrt 2 • recovery ((f : GaussianL2)+(g : GaussianL2))=_
        rw [recovery_add,smul_add]
        rfl
      map_smul' c f := by
        apply Subtype.ext
        change Real.sqrt 2 • recovery (c • (f : GaussianL2))=c • (Real.sqrt 2 • recovery f)
        rw [recovery_smul,smul_comm (Real.sqrt 2) c] }
  norm_map' f := by
    change ‖Real.sqrt 2 • recovery (f : GaussianL2)‖=‖(f : GaussianL2)‖
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    have he : (Real.sqrt 2*‖recovery f‖)^2=‖(f : GaussianL2)‖^2 := by
      rw [mul_pow,hs,second_recovery_energy f.property]
      ring
    exact (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp he

theorem quadraticLift_surjective : Function.Surjective quadraticLift := by
  intro v
  let f : sector 2 := ⟨(Real.sqrt 2)⁻¹ • completedDivergence v,
    (sector 2).smul_mem _ (completedDivergence_mem_sector_two v.property.1)⟩
  refine ⟨f,Subtype.ext ?_⟩
  change Real.sqrt 2 • recovery ((Real.sqrt 2)⁻¹ • completedDivergence (v : GaussianVectorL2))=(v : GaussianVectorL2)
  rw [recovery_smul,completed_recovery v.property.1]
  have hp : gradientProjection (v : GaussianVectorL2)=v := gradientRange.starProjection_eq_self_iff.mpr v.property.2
  rw [hp,smul_smul,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2))),one_smul]

def quadraticUnitary : sector 2 ≃ₗᵢ[ℝ] symmetricFields :=
  LinearIsometryEquiv.ofSurjective quadraticLift quadraticLift_surjective

end OperatorDerivativeRewrite.Foundation.GaussianQuadraticRecoverySurjectivity




