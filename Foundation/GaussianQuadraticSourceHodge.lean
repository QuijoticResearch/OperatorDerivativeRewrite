import Foundation.GaussianSourceHodge
import Foundation.GaussianWickRecoveryPrediction
import Foundation.DivergenceKernelContrast
import Mathlib.Data.Matrix.Basic

/-! Actual Gaussian source Hodge decomposition on linear random matrix fields. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.GaussianQuadraticSourceHodge
open InfiniteGaussian GaussianNumberSectors GaussianDivergenceRecovery GaussianSourceHodge
open GaussianTimePolynomialPairing GaussianTimeSensitivity GaussianQuadraticIncrement GaussianTimeFieldNorm
open DivergenceKernelContrast

theorem recovery_mem_gradientRange (f : GaussianL2) : recovery f∈gradientRange := by
  rw [← gradientRange.orthogonal_orthogonal]
  apply (gradientRangeᗮ).mem_orthogonal (recovery f) |>.mpr
  intro v hv
  exact recovery_orthogonal_kernel f v ((gradientRange_orthogonal_iff_divergence_zero v).mp hv)

private theorem divergence_target_zero_mode {v : GaussianVectorL2} {f : GaussianL2}
    (hg : (v,f)∈hilbertDivergence.graph) : projection 0 f=0 := by
  have hi := GaussianNumberSectors.graph_duality (closedDerivative_constant_graph 1) hg
  have hc : inner ℝ gaussianOne f=0 := by simpa only [one_smul,inner_zero_left] using hi.symm
  rw [projection_zero,hc,zero_smul]

theorem recovery_divergence_gradientProjection (v : GaussianVectorL2) (f : GaussianL2)
    (hg : (v,f)∈hilbertDivergence.graph) : recovery f=gradientProjection v := by
  have hr := recovery_graph f
  rw [divergence_target_zero_mode hg,sub_zero] at hr
  have hz : (v-recovery f,0)∈hilbertDivergence.graph := by
    simpa only [Prod.mk_sub_mk,sub_self] using hilbertDivergence.graph.sub_mem hg hr
  exact ((gradientRange).eq_starProjection_of_mem_orthogonal (recovery_mem_gradientRange f)
    ((gradientRange_orthogonal_iff_divergence_zero _).mpr hz)).symm

def mixedPolynomial (u v : CoefficientSpace) : polynomialCylindricalDomain :=
  polynomialProduct (firstChaosPolynomial u) (firstChaosPolynomial v)-inner ℝ u v • oneCore

def mixedTarget (u v : CoefficientSpace) : GaussianL2 := mixedPolynomial u v

theorem mixedTarget_coeFn (u v : CoefficientSpace) :
    mixedTarget u v =ᵐ[gaussianProduct] fun ω => firstChaosEmbedding u ω*firstChaosEmbedding v ω-inner ℝ u v := by
  filter_upwards [Lp.coeFn_sub (polynomialProduct (firstChaosPolynomial u) (firstChaosPolynomial v) : GaussianL2)
      (inner ℝ u v • (oneCore : GaussianL2)),
    polynomialProductL2_coeFn (firstChaosPolynomial u) (firstChaosPolynomial v),
    firstChaosPolynomial_coeFn u,firstChaosPolynomial_coeFn v,Lp.coeFn_smul (inner ℝ u v) (oneCore : GaussianL2),
    oneCore_eq.symm ▸ gaussianOne_coeFn] with ω hs hp hu hv hm h1
  change ((polynomialProduct (firstChaosPolynomial u) (firstChaosPolynomial v) : GaussianL2)-
    inner ℝ u v • (oneCore : GaussianL2)) ω=(firstChaosEmbedding u) ω*(firstChaosEmbedding v) ω-inner ℝ u v
  rw [hs,Pi.sub_apply]
  change polynomialProductL2 (firstChaosPolynomial u) (firstChaosPolynomial v) ω-
    (inner ℝ u v • (oneCore : GaussianL2)) ω=_
  rw [hp,hu,hv,hm,Pi.smul_apply,h1,smul_eq_mul,mul_one]

theorem mixedTarget_rankDivergence (u v : CoefficientSpace) :
    mixedTarget u v=rankDivergence (firstChaosPolynomial v) u := by
  apply Lp.ext
  filter_upwards [mixedTarget_coeFn u v,rankDivergence_coeFn (firstChaosPolynomial v) u,
    firstChaosPolynomial_coeFn v,firstChaosPolynomial_derivative_coeFn v] with ω hm hr hv hd
  rw [hm,hr,hv,hd,real_inner_comm u v]
  ring

theorem mixed_derivative (u v : CoefficientSpace) :
    polynomialDerivative (mixedPolynomial u v)=
      scalarTensor u (firstChaosEmbedding v)+scalarTensor v (firstChaosEmbedding u) := by
  rw [mixedPolynomial,map_sub,map_smul,oneCore_derivative,smul_zero,sub_zero,
    polynomialDerivative_product,polynomialTimesDerivative_firstChaos,polynomialTimesDerivative_firstChaos,
    firstChaosPolynomial_eq_embedding,firstChaosPolynomial_eq_embedding,add_comm]

theorem mixed_derivative_graph (u v : CoefficientSpace) :
    (mixedTarget u v,scalarTensor u (firstChaosEmbedding v)+scalarTensor v (firstChaosEmbedding u))
      ∈closedCylindricalDerivative.graph := by
  have hg := closedCylindricalDerivative_core_graph (mixedPolynomial u v)
  simpa only [mixed_derivative,mixedTarget] using hg

theorem mixed_divergence_graph (u v : CoefficientSpace) :
    (scalarTensor u (firstChaosEmbedding v),mixedTarget u v)∈hilbertDivergence.graph := by
  have hg := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (firstChaosPolynomial v) u)
  rw [firstChaosPolynomial_eq_embedding,← mixedTarget_rankDivergence] at hg
  exact hg

def mixedSource (u v : CoefficientSpace) : GaussianVectorL2 :=
  (1/2 : ℝ) • (scalarTensor u (firstChaosEmbedding v)+scalarTensor v (firstChaosEmbedding u))

theorem mixedSource_gradient (u v : CoefficientSpace) : mixedSource u v∈gradientRange := by
  apply (mem_gradientRange_iff _).mpr
  refine ⟨(1/2 : ℝ) • mixedTarget u v, ?_⟩
  simpa only [Prod.smul_mk,mixedSource] using closedCylindricalDerivative.graph.smul_mem (1/2 : ℝ)
    (mixed_derivative_graph u v)

theorem linear_rank_gradientProjection (u v : CoefficientSpace) :
    gradientProjection (scalarTensor u (firstChaosEmbedding v))=mixedSource u v := by
  have he : scalarTensor u (firstChaosEmbedding v)-mixedSource u v=(1/2 : ℝ) • skewField u v := by
    rw [mixedSource,skewField]
    module
  apply gradientRange.eq_starProjection_of_mem_orthogonal (mixedSource_gradient u v)
  apply (gradientRange_orthogonal_iff_divergence_zero _).mpr
  rw [he]
  simpa only [Prod.smul_mk,smul_zero] using hilbertDivergence.graph.smul_mem (1/2 : ℝ) (skewField_divergence_zero u v)

theorem recovery_mixed (u v : CoefficientSpace) : recovery (mixedTarget u v)=mixedSource u v := by
  rw [recovery_divergence_gradientProjection _ _ (mixed_divergence_graph u v),linear_rank_gradientProjection]

section MatrixFields
variable {I : Type*} [Fintype I]

def linearField (h : I → CoefficientSpace) (A : Matrix I I ℝ) : GaussianVectorL2 :=
  ∑ i, ∑ j, A i j • scalarTensor (h i) (firstChaosEmbedding (h j))

def quadraticTarget (h : I → CoefficientSpace) (A : Matrix I I ℝ) : GaussianL2 :=
  ∑ i, ∑ j, A i j • mixedTarget (h i) (h j)

def symmetrize (A : Matrix I I ℝ) : Matrix I I ℝ := fun i j => (A i j+A j i)/2

theorem linearField_add (h : I → CoefficientSpace) (A B : Matrix I I ℝ) :
    linearField h (A+B)=linearField h A+linearField h B := by
  simp only [linearField,Matrix.add_apply,add_smul,Finset.sum_add_distrib]

theorem linearField_smul (h : I → CoefficientSpace) (c : ℝ) (A : Matrix I I ℝ) :
    linearField h (c • A)=c • linearField h A := by
  simp only [linearField,Matrix.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul]

theorem linearField_symmetrize (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    linearField h (symmetrize A)=(1/2 : ℝ) • (linearField h A+linearField h A.transpose) := by
  have he : symmetrize A=(1/2 : ℝ) • (A+A.transpose) := by
    funext i j
    change (A i j+A j i)/2=(1/2 : ℝ)*(A i j+A j i)
    ring
  rw [he,linearField_smul,linearField_add]

private theorem swapped_field_sum (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    (∑ i, ∑ j, A i j • scalarTensor (h j) (firstChaosEmbedding (h i)))=linearField h A.transpose := by
  rw [Finset.sum_comm]
  rfl

private theorem symmetric_field_sum (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    (∑ i, ∑ j, A i j • (scalarTensor (h i) (firstChaosEmbedding (h j))+
      scalarTensor (h j) (firstChaosEmbedding (h i))))=linearField h A+linearField h A.transpose := by
  simp only [smul_add,Finset.sum_add_distrib]
  rw [swapped_field_sum]
  rfl

theorem linearField_divergence_graph (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    (linearField h A,quadraticTarget h A)∈hilbertDivergence.graph := by
  unfold linearField quadraticTarget
  rw [prod_mk_sum]
  apply hilbertDivergence.graph.sum_mem
  intro i hi
  rw [prod_mk_sum]
  apply hilbertDivergence.graph.sum_mem
  intro j hj
  simpa only [Prod.smul_mk] using hilbertDivergence.graph.smul_mem (A i j) (mixed_divergence_graph (h i) (h j))

theorem quadraticTarget_derivative_graph (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    (quadraticTarget h A,linearField h A+linearField h A.transpose)∈closedCylindricalDerivative.graph := by
  rw [← symmetric_field_sum]
  unfold quadraticTarget
  rw [prod_mk_sum]
  apply closedCylindricalDerivative.graph.sum_mem
  intro i hi
  rw [prod_mk_sum]
  apply closedCylindricalDerivative.graph.sum_mem
  intro j hj
  simpa only [Prod.smul_mk] using closedCylindricalDerivative.graph.smul_mem (A i j) (mixed_derivative_graph (h i) (h j))

theorem quadraticTarget_recovery (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    recovery (quadraticTarget h A)=linearField h (symmetrize A) := by
  change recoveryOperator (∑ i, ∑ j, A i j • mixedTarget (h i) (h j))=_
  simp only [map_sum,map_smul]
  change (∑ i, ∑ j, A i j • recovery (mixedTarget (h i) (h j)))=_
  simp_rw [recovery_mixed,mixedSource]
  calc
    _=(1/2 : ℝ) • ∑ i, ∑ j, A i j • (scalarTensor (h i) (firstChaosEmbedding (h j))+
        scalarTensor (h j) (firstChaosEmbedding (h i))) := by
      simp only [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact smul_comm _ _ _
    _=(1/2 : ℝ) • (linearField h A+linearField h A.transpose) := by rw [symmetric_field_sum]
    _=linearField h (symmetrize A) := (linearField_symmetrize h A).symm

theorem linearField_gradientProjection (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    gradientProjection (linearField h A)=linearField h (symmetrize A) := by
  rw [← recovery_divergence_gradientProjection _ _ (linearField_divergence_graph h A),quadraticTarget_recovery]

theorem quadraticTarget_variance (h : I → CoefficientSpace) (A : Matrix I I ℝ) :
    ‖quadraticTarget h A‖^2=2*‖linearField h (symmetrize A)‖^2 := by
  have hd := quadraticTarget_derivative_graph h A
  have he : linearField h A+linearField h A.transpose=(2 : ℝ) • linearField h (symmetrize A) := by
    rw [linearField_symmetrize,smul_smul]
    norm_num
  rw [he] at hd
  have hr := recovery_graph (quadraticTarget h A)
  rw [divergence_target_zero_mode (linearField_divergence_graph h A),sub_zero,quadraticTarget_recovery] at hr
  have hi := GaussianNumberSectors.graph_duality hd hr
  rw [real_inner_smul_left,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hi
  exact hi.symm

theorem linearField_inner (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A B : Matrix I I ℝ) :
    inner ℝ (linearField h A) (linearField h B)=∑ i, ∑ j, A i j*B i j := by
  classical
  simp only [linearField,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,
    scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map]
  have hc := orthonormal_iff_ite.mp hh
  simp_rw [hc]
  simp [mul_ite,ite_mul,mul_assoc,mul_comm]

theorem linearField_energy (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A : Matrix I I ℝ) :
    ‖linearField h A‖^2=∑ i, ∑ j, (A i j)^2 := by
  rw [← real_inner_self_eq_norm_sq,linearField_inner h hh]
  simp only [pow_two]

theorem quadraticTarget_matrix_energy (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A : Matrix I I ℝ) :
    ‖quadraticTarget h A‖^2=2*∑ i, ∑ j, ((A i j+A j i)/2)^2 := by
  rw [quadraticTarget_variance,linearField_energy h hh]
  rfl

theorem linearField_divergence_kernel_iff (h : I → CoefficientSpace) (hh : Orthonormal ℝ h) (A : Matrix I I ℝ) :
    (linearField h A,0)∈hilbertDivergence.graph ↔ ∀ i j, A i j=-A j i := by
  classical
  constructor
  · intro hg
    have hp := recovery_divergence_gradientProjection _ _ hg
    have hz : recovery (0 : GaussianL2)=0 := by change recoveryOperator 0=0; exact map_zero _
    rw [hz,linearField_gradientProjection] at hp
    have he := linearField_energy h hh (symmetrize A)
    rw [← hp,norm_zero] at he
    intro i j
    have hi := Finset.single_le_sum (s := Finset.univ) (fun k hk => show 0≤∑ l, (symmetrize A k l)^2 by positivity)
      (Finset.mem_univ i)
    have hj := Finset.single_le_sum (s := Finset.univ) (fun l hl => sq_nonneg (symmetrize A i l)) (Finset.mem_univ j)
    have hs : (symmetrize A i j)^2=0 := by nlinarith [hj.trans hi]
    have h0 := sq_eq_zero_iff.mp hs
    dsimp [symmetrize] at h0
    linarith
  · intro hA
    have he : symmetrize A=0 := by
      funext i j
      change (A i j+A j i)/2=0
      rw [hA i j]
      ring
    have hp : gradientProjection (linearField h A)=0 := by
      rw [linearField_gradientProjection,he]
      simp [linearField]
    simpa only [hp,sub_zero] using residual_divergence_zero (linearField h A)

end MatrixFields
end OperatorDerivativeRewrite.Foundation.GaussianQuadraticSourceHodge



