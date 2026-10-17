import Foundation.GaussianCubicConditionalPrediction
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Projection form of the quadratic Schur mechanism, including dependent interior modes. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SchurGaussianInnovation
set_option backward.isDefEq.respectTransparency false
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection

variable {I : Type*}

def residual (h : I → CoefficientSpace) (v : CoefficientSpace) : CoefficientSpace :=
  v-sourceProjection h v

def effectiveCurvature (h : I → CoefficientSpace) (v : CoefficientSpace) : ℝ :=
  ‖residual h v‖^2

/-- Completing the square needs a closed span, not an invertible Gram matrix. -/
theorem completed_square (h : I → CoefficientSpace) (v z : CoefficientSpace)
    (hz : z ∈ sourceSpan h) :
    ‖v-z‖^2 = effectiveCurvature h v + ‖sourceProjection h v-z‖^2 := by
  have hm := (sourceSpan h).sub_mem ((sourceSpan h).starProjection_apply_mem v) hz
  have ho := (sourceSpan h).starProjection_inner_eq_zero v (sourceProjection h v-z) hm
  change inner ℝ (v-sourceProjection h v) (sourceProjection h v-z)=0 at ho
  have he : v-z=(v-sourceProjection h v)+(sourceProjection h v-z) := by abel
  rw [he, norm_add_sq_real, ho]
  simp [effectiveCurvature, residual]

theorem energy_lower_bound (h : I → CoefficientSpace) (v z : CoefficientSpace)
    (hz : z ∈ sourceSpan h) : effectiveCurvature h v ≤ ‖v-z‖^2 := by
  rw [completed_square h v z hz]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem sourceSpan_eq_span [Fintype I] (h : I → CoefficientSpace) :
    sourceSpan h = Submodule.span ℝ (Set.range h) := by
  let S := Submodule.span ℝ (Set.range h)
  let : FiniteDimensional ℝ S := FiniteDimensional.span_of_finite ℝ (Set.finite_range h)
  exact S.closed_of_finiteDimensional.submodule_topologicalClosure_eq

theorem interior_mem [Fintype I] (h : I → CoefficientSpace) (y : I → ℝ) :
    (∑ i, y i • h i) ∈ sourceSpan h := by
  apply (sourceSpan h).sum_mem
  intro i _
  exact (sourceSpan h).smul_mem _
    ((Submodule.span ℝ (Set.range h)).le_topologicalClosure (Submodule.subset_span ⟨i,rfl⟩))

theorem finite_interior_lower_bound [Fintype I] (h : I → CoefficientSpace)
    (v : CoefficientSpace) (y : I → ℝ) :
    effectiveCurvature h v ≤ ‖v-∑ i, y i • h i‖^2 :=
  energy_lower_bound h v _ (interior_mem h y)

/-- The finite least-squares minimum is attained even when the columns are dependent. -/
theorem finite_minimum_attained [Fintype I] (h : I → CoefficientSpace) (v : CoefficientSpace) :
    ∃ y : I → ℝ, ‖v-∑ i, y i • h i‖^2 = effectiveCurvature h v := by
  have hm : sourceProjection h v ∈ Submodule.span ℝ (Set.range h) :=
    (sourceSpan_eq_span h).le ((sourceSpan h).starProjection_apply_mem v)
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hm
  exact ⟨y, by rw [hy]; rfl⟩

theorem effectiveCurvature_nonneg (h : I → CoefficientSpace) (v : CoefficientSpace) :
    0 ≤ effectiveCurvature h v := sq_nonneg _

theorem effectiveCurvature_zero_iff (h : I → CoefficientSpace) (v : CoefficientSpace) :
    effectiveCurvature h v=0 ↔ v ∈ sourceSpan h := by
  constructor
  · intro he
    change ‖residual h v‖^2=0 at he
    have hn : ‖residual h v‖=0 := by nlinarith [norm_nonneg (residual h v)]
    have hr := norm_eq_zero.mp hn
    change v-sourceProjection h v=0 at hr
    exact (sourceSpan h).starProjection_eq_self_iff.mp (sub_eq_zero.mp hr).symm
  · intro hv
    have hp : sourceProjection h v=v := (sourceSpan h).starProjection_eq_self_iff.mpr hv
    simp [effectiveCurvature, residual, hp]

theorem effectiveCurvature_le (h : I → CoefficientSpace) (v : CoefficientSpace) :
    effectiveCurvature h v ≤ ‖v‖^2 := by
  simpa using energy_lower_bound h v 0 (sourceSpan h).zero_mem

theorem effectiveCurvature_smul (h : I → CoefficientSpace) (v : CoefficientSpace) (x : ℝ) :
    effectiveCurvature h (x • v) = x^2*effectiveCurvature h v := by
  simp [effectiveCurvature, residual, map_smul, ← smul_sub, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]

theorem core_energy_lower_bound [Fintype I] (h : I → CoefficientSpace)
    (v : CoefficientSpace) (x : ℝ) (y : I → ℝ) :
    x^2*effectiveCurvature h v ≤ ‖(∑ i, y i • h i)+x • v‖^2 := by
  have he := energy_lower_bound h (x • v) (-(∑ i, y i • h i))
    ((sourceSpan h).neg_mem (interior_mem h y))
  simpa only [effectiveCurvature_smul, sub_neg_eq_add, add_comm] using he

theorem core_minimum_attained [Fintype I] (h : I → CoefficientSpace)
    (v : CoefficientSpace) (x : ℝ) :
    ∃ y : I → ℝ, ‖(∑ i, y i • h i)+x • v‖^2=x^2*effectiveCurvature h v := by
  obtain ⟨y, hy⟩ := finite_minimum_attained h (x • v)
  refine ⟨fun i => -y i, ?_⟩
  simp only [neg_smul, Finset.sum_neg_distrib]
  rw [add_comm, ← sub_eq_add_neg, hy, effectiveCurvature_smul]

theorem conditional_innovation (h : I → CoefficientSpace) (v : CoefficientSpace) :
    firstChaosEmbedding v-conditionalProjection h (firstChaosEmbedding v) =
      firstChaosEmbedding (residual h v) := by
  rw [conditional_firstChaos_projection, residual, map_sub]

/-- The exact surviving quadratic curvature is the actual Gaussian prediction error energy. -/
theorem conditional_error_energy (h : I → CoefficientSpace) (v : CoefficientSpace) :
    ‖firstChaosEmbedding v-conditionalProjection h (firstChaosEmbedding v)‖^2 =
      effectiveCurvature h v := by
  rw [conditional_innovation, firstChaos_norm]
  rfl

theorem effectiveCurvature_eq_residualVariance (h : I → CoefficientSpace) (v : CoefficientSpace) :
    effectiveCurvature h v = GaussianCubicConditionalPrediction.residualVariance h v :=
  (GaussianCubicConditionalPrediction.residualVariance_eq_norm_sq h v).symm

theorem unscreenable_projection (h : I → CoefficientSpace) (v : CoefficientSpace)
    (hv : ∀ i, inner ℝ v (h i)=0) : sourceProjection h v=0 := by
  have hs : Submodule.span ℝ (Set.range h) ≤ (innerSL ℝ v).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hv i
  have hc := (Submodule.span ℝ (Set.range h)).topologicalClosure_minimal hs
    (innerSL ℝ v).isClosed_ker
  have ho : v ∈ (sourceSpan h)ᗮ := by
    apply (sourceSpan h).mem_orthogonal v |>.mpr
    intro z hz
    have he := hc hz
    change inner ℝ v z=0 at he
    simpa only [real_inner_comm] using he
  exact (sourceSpan h).eq_starProjection_of_mem_orthogonal (sourceSpan h).zero_mem
    (by simpa only [sub_zero] using ho)

theorem unscreenable_curvature (h : I → CoefficientSpace) (v : CoefficientSpace)
    (hv : ∀ i, inner ℝ v (h i)=0) : effectiveCurvature h v=‖v‖^2 := by
  simp [effectiveCurvature, residual, unscreenable_projection h v hv]

theorem unscreenable_conditional_mean (h : I → CoefficientSpace) (v : CoefficientSpace)
    (hv : ∀ i, inner ℝ v (h i)=0) :
    conditionalProjection h (firstChaosEmbedding v)=0 := by
  rw [conditional_firstChaos_projection, unscreenable_projection h v hv, map_zero]

def synthesis {P : Type*} [Fintype P] (b : P → CoefficientSpace) (a : P → ℝ) :
    CoefficientSpace := ∑ p, a p • b p

theorem synthesis_inner {P : Type*} [Fintype P] (b : P → CoefficientSpace)
    (hb : Orthonormal ℝ b) (a c : P → ℝ) :
    inner ℝ (synthesis b a) (synthesis b c) = ∑ p, a p*c p := by
  simpa [synthesis] using hb.inner_sum a c Finset.univ

theorem synthesis_norm_sq {P : Type*} [Fintype P] (b : P → CoefficientSpace)
    (hb : Orthonormal ℝ b) (a : P → ℝ) : ‖synthesis b a‖^2=∑ p, (a p)^2 := by
  rw [← real_inner_self_eq_norm_sq, synthesis_inner b hb]
  simp only [pow_two]

def columns {P : Type*} [Fintype P] (b : P → CoefficientSpace) (A : P → I → ℝ) :
    I → CoefficientSpace := fun i => synthesis b (fun p => A p i)

theorem incidence_pairing {P : Type*} [Fintype P] (b : P → CoefficientSpace)
    (hb : Orthonormal ℝ b) (A : P → I → ℝ) (v : P → ℝ) (i : I) :
    inner ℝ (synthesis b v) (columns b A i) = ∑ p, v p*A p i :=
  synthesis_inner b hb v (fun p => A p i)

/-- The left-kernel condition is exactly an unscreenable actual Gaussian source direction. -/
theorem incidence_unscreenable {P : Type*} [Fintype P] (b : P → CoefficientSpace)
    (hb : Orthonormal ℝ b) (A : P → I → ℝ) (v : P → ℝ)
    (hv : ∀ i, ∑ p, v p*A p i=0) :
    effectiveCurvature (columns b A) (synthesis b v) = ∑ p, (v p)^2 := by
  rw [unscreenable_curvature (columns b A) (synthesis b v)
    (fun i => (incidence_pairing b hb A v i).trans (hv i)), synthesis_norm_sq b hb]

/-- Conservative columns protect the uniform mode, with no rank or Gram inverse assumption. -/
theorem conservative_uniform_curvature {P : Type*} [Fintype P] (b : P → CoefficientSpace)
    (hb : Orthonormal ℝ b) (A : P → I → ℝ) (hA : ∀ i, ∑ p, A p i=0) :
    effectiveCurvature (columns b A) (synthesis b (fun _ => 1)) = Fintype.card P := by
  rw [incidence_unscreenable b hb A (fun _ => 1) (by simpa using hA)]
  simp

theorem conservative_uniform_prediction_error {P : Type*} [Fintype P]
    (b : P → CoefficientSpace) (hb : Orthonormal ℝ b) (A : P → I → ℝ)
    (hA : ∀ i, ∑ p, A p i=0) :
    ‖firstChaosEmbedding (synthesis b (fun _ => 1))-
      conditionalProjection (columns b A) (firstChaosEmbedding (synthesis b (fun _ => 1)))‖^2 =
        Fintype.card P := by
  rw [conditional_error_energy, conservative_uniform_curvature b hb A hA]

def signedIncidence {P : Type*} [DecidableEq P] (s t : I → P) (p : P) (i : I) : ℝ :=
  (if p=s i then 1 else 0)-(if p=t i then 1 else 0)

theorem signedIncidence_conservative {P : Type*} [Fintype P] [DecidableEq P]
    (s t : I → P) (i : I) : ∑ p, signedIncidence s t p i=0 := by
  simp [signedIncidence, Finset.sum_sub_distrib]

theorem four_constraint_curvature (b : Fin 4 → CoefficientSpace) (hb : Orthonormal ℝ b)
    (s t : I → Fin 4) :
    effectiveCurvature (columns b (signedIncidence s t)) (synthesis b (fun _ => 1))=4 := by
  simpa using conservative_uniform_curvature b hb (signedIncidence s t)
    (signedIncidence_conservative s t)

def duplicateColumns (u : CoefficientSpace) : Fin 2 → CoefficientSpace := fun _ => u

def redundantKernel : Fin 2 → ℝ := ![1,-1]

theorem redundantKernel_nonzero : redundantKernel ≠ 0 := by
  intro he
  have := congrFun he 0
  norm_num [redundantKernel] at this

theorem duplicate_kernel (u : CoefficientSpace) :
    (∑ i, redundantKernel i • duplicateColumns u i)=0 := by
  simp [Fin.sum_univ_two, redundantKernel, duplicateColumns]

theorem duplicate_unscreenable (u v : CoefficientSpace) (hv : inner ℝ v u=0) :
    effectiveCurvature (duplicateColumns u) v=‖v‖^2 :=
  unscreenable_curvature _ _ (fun _ => hv)

theorem duplicate_screened (u : CoefficientSpace) : effectiveCurvature (duplicateColumns u) u=0 := by
  apply (effectiveCurvature_zero_iff _ _).mpr
  exact (Submodule.span ℝ (Set.range (duplicateColumns u))).le_topologicalClosure
    (Submodule.subset_span ⟨(0 : Fin 2), rfl⟩)

end OperatorDerivativeRewrite.Foundation.SchurGaussianInnovation
