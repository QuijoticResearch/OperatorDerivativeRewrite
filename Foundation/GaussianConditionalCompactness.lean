import Foundation.GaussianRecoveryCompactnessObstruction
import Foundation.GaussianWickConditionalProjection
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Exact compactness classification for actual Gaussian conditional projections. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianConditionalCompactness
open InfiniteGaussian GaussianTimeSpaceHermite GaussianConditionalGraph GaussianWickConditionalProjection

def normalizedWick (u : CoefficientSpace) (n : ℕ) : GaussianL2 :=
  (Real.sqrt (n.factorial : ℝ))⁻¹ • (wick u n : GaussianL2)

theorem normalizedWick_orthonormal (u : CoefficientSpace) (hu : ‖u‖^2=1) :
    Orthonormal ℝ (normalizedWick u) := by
  rw [orthonormal_iff_ite]
  intro n m
  simp only [normalizedWick,real_inner_smul_left,real_inner_smul_right,wick_inner,
    real_inner_self_eq_norm_sq,hu,one_pow]
  by_cases hn : n=m
  · subst m
    simp only [if_pos rfl,mul_one]
    have hp : Real.sqrt (n.factorial : ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    have hs := Real.sq_sqrt (show (0 : ℝ)≤n.factorial by positivity)
    field_simp
    simp only [ite_true,mul_one]
    nlinarith [hs]
  · simp [hn]

def terminalEmbedding (u : CoefficientSpace) (hu : ‖u‖^2=1) : CoefficientSpace →ₗᵢ[ℝ] GaussianL2 :=
  (normalizedWick_orthonormal u hu).orthogonalFamily.linearIsometry

theorem terminalEmbedding_hasSum (u : CoefficientSpace) (hu : ‖u‖^2=1) (c : CoefficientSpace) :
    HasSum (fun n => c n • normalizedWick u n) (terminalEmbedding u hu c) := by
  simpa only [terminalEmbedding,LinearIsometry.toSpanSingleton_apply] using
    (normalizedWick_orthonormal u hu).orthogonalFamily.hasSum_linearIsometry c

theorem conditional_fixes_terminalEmbedding {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (hm : u∈sourceSpan h) (c : CoefficientSpace) :
    conditionalProjection h (terminalEmbedding u hu c)=terminalEmbedding u hu c := by
  have hn (n : ℕ) : conditionalProjection h (normalizedWick u n)=normalizedWick u n := by
    apply Submodule.starProjection_eq_self_iff.mpr
    exact (generated h).smul_mem _ (wick_mem_generated_of_sourceSpan h u hm n)
  have hs := (conditionalProjection h).hasSum (terminalEmbedding_hasSum u hu c)
  simp only [map_smul,hn] at hs
  exact hs.unique (terminalEmbedding_hasSum u hu c)

theorem unit_observation_noncompact {I : Type*} (h : I → CoefficientSpace)
    (u : CoefficientSpace) (hu : ‖u‖^2=1) (hm : u∈sourceSpan h) :
    ¬ IsCompactOperator (conditionalProjection h) := by
  let U := (terminalEmbedding u hu).toContinuousLinearMap
  have hid : U.adjoint.comp ((conditionalProjection h).comp U)=ContinuousLinearMap.id ℝ CoefficientSpace := by
    apply ContinuousLinearMap.ext
    intro x
    apply ext_inner_right ℝ
    intro y
    rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_left,
      ContinuousLinearMap.id_apply]
    change inner ℝ (conditionalProjection h (terminalEmbedding u hu x)) (terminalEmbedding u hu y)=inner ℝ x y
    rw [conditional_fixes_terminalEmbedding h u hu hm,(terminalEmbedding u hu).inner_map_map]
  intro hc
  have hi := (hc.comp_clm U).clm_comp U.adjoint
  change IsCompactOperator (U.adjoint.comp ((conditionalProjection h).comp U)) at hi
  rw [hid] at hi
  exact GaussianRecoveryCompactnessObstruction.coefficient_space_not_finiteDimensional
    (isCompactOperator_id_iff_finiteDimensional.mp hi)

theorem nonzero_observation_noncompact {I : Type*} (h : I → CoefficientSpace)
    (i : I) (hi : h i≠0) : ¬ IsCompactOperator (conditionalProjection h) := by
  let u := ‖h i‖⁻¹ • h i
  have hp : 0<‖h i‖ := norm_pos_iff.mpr hi
  have hu : ‖u‖^2=1 := by
    dsimp [u]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),inv_mul_cancel₀ (ne_of_gt hp)]
    norm_num
  have hm : u∈sourceSpan h :=
    (sourceSpan h).smul_mem _ ((Submodule.span ℝ (Set.range h)).le_topologicalClosure
      (Submodule.subset_span ⟨i,rfl⟩))
  exact unit_observation_noncompact h u hu hm

theorem zero_family_polynomial_constant {I : Type*} (h : I → CoefficientSpace) (hz : ∀ i, h i=0)
    (p : MvPolynomial I ℝ) : familyPolynomialEmbedding h p=MvPolynomial.eval (fun _ => 0) p • gaussianOne := by
  apply Lp.ext
  filter_upwards [isonormalCylinderL2_coeFn h p,Lp.coeFn_smul (MvPolynomial.eval (fun _ => (0 : ℝ)) p) gaussianOne,
    gaussianOne_coeFn,Lp.coeFn_zero ℝ 2 gaussianProduct] with ω hp hs ho hz'
  change isonormalCylinderL2 h p ω=_ at hp ⊢
  rw [hp,hs]
  simp only [Pi.smul_apply,smul_eq_mul,ho,mul_one]
  simp only [isonormalCylinder,hz,map_zero,hz',Pi.zero_apply]

theorem zero_family_generated {I : Type*} (h : I → CoefficientSpace) (hz : ∀ i, h i=0) :
    generated h=Submodule.span ℝ {gaussianOne} := by
  apply le_antisymm
  · rw [generated,← familyPolynomial_closure]
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨p,rfl⟩
      rw [zero_family_polynomial_constant h hz p]
      exact (Submodule.span ℝ {gaussianOne}).smul_mem _ (Submodule.subset_span (by simp))
    · exact Submodule.closed_of_finiteDimensional _
  · have hm := wick_mem_generated_of_sourceSpan h 0 (sourceSpan h).zero_mem 0
    have hone : gaussianOne∈generated h := by simpa only [wick,core_zero] using hm
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hone)
theorem zero_family_projection {I : Type*} (h : I → CoefficientSpace) (hz : ∀ i, h i=0) (f : GaussianL2) :
    conditionalProjection h f=inner ℝ gaussianOne f • gaussianOne := by
  have hn : ‖gaussianOne‖^2=1 := by
    rw [← real_inner_self_eq_norm_sq,GaussianDeterministicGraphCore.gaussianOne_inner_self]
  change (generated h).starProjection f=inner ℝ gaussianOne f • gaussianOne
  simp [zero_family_generated h hz,Submodule.starProjection_singleton,hn]

theorem zero_family_compact {I : Type*} (h : I → CoefficientSpace) (hz : ∀ i, h i=0) :
    IsCompactOperator (conditionalProjection h) := by
  have he : conditionalProjection h=(innerSL ℝ gaussianOne).smulRight gaussianOne := by
    apply ContinuousLinearMap.ext
    intro f
    exact zero_family_projection h hz f
  rw [he]
  have hc := isCompactOperator_of_locallyCompactSpace_rng ((ContinuousLinearMap.id ℝ ℝ).smulRight gaussianOne)
  exact hc.comp_clm (innerSL ℝ gaussianOne)

theorem conditionalProjection_compact_iff {I : Type*} (h : I → CoefficientSpace) :
    IsCompactOperator (conditionalProjection h) ↔ ∀ i, h i=0 := by
  constructor
  · intro hc i
    by_contra hi
    exact nonzero_observation_noncompact h i hi hc
  · exact zero_family_compact h

end OperatorDerivativeRewrite.Foundation.GaussianConditionalCompactness


