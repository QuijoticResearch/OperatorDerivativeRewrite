import Foundation.PoissonAdjoints
import Foundation.GaussianTimePolynomialPairing

/-! Divergence kernels distinguish the one-count Poisson model from a
Gaussian source with two independent directions. This is a dimensional
comparison, not a claim about every Poisson noise space. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
set_option backward.isDefEq.respectTransparency false

namespace OperatorDerivativeRewrite.Foundation.DivergenceKernelContrast
open PoissonDifferenceCore PoissonDifferenceOperators PoissonMaximalOperators PoissonCoordinateEvaluation
open InfiniteGaussian GaussianTimePolynomialPairing GaussianTimeFieldNorm

theorem poisson_divergence_zero_iff (rate : ℝ≥0) (hr : 0 < rate) (u : FieldL2 rate) :
    (u,0) ∈ (maximalDivergence rate hr).graph ↔ u=0 := by
  constructor
  · intro hu
    rw [maximalDivergence_graph] at hu
    have hp : (rate : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
    have he (k : ℕ) : u k=0 := by
      induction k with
      | zero =>
        have h := hu 0
        rw [scalar_zero_apply rate hr] at h
        change 0 = -(rate : ℝ)*u 0 at h
        exact (mul_eq_zero.mp (show (rate : ℝ)*u 0=0 by linarith)).resolve_left hp
      | succ k ih =>
        have h := hu (k+1)
        rw [scalar_zero_apply rate hr] at h
        change 0 = (k+1 : ℝ)*u k-(rate : ℝ)*u (k+1) at h
        rw [ih,mul_zero,zero_sub] at h
        exact (mul_eq_zero.mp (show (rate : ℝ)*u (k+1)=0 by linarith)).resolve_left hp
    apply Lp.ext
    filter_upwards [] with k
    rw [field_zero_apply rate hr,he]
  · intro hu
    subst u
    exact (maximalDivergence rate hr).graph.zero_mem

theorem firstChaosPolynomial_eq_embedding (h : CoefficientSpace) :
    (firstChaosPolynomial h : GaussianL2) = firstChaosEmbedding h :=
  Lp.ext (firstChaosPolynomial_coeFn h)

theorem rankDivergence_linear_symmetric (h k : CoefficientSpace) :
    rankDivergence (firstChaosPolynomial k) h = rankDivergence (firstChaosPolynomial h) k := by
  apply Lp.ext
  filter_upwards [rankDivergence_coeFn (firstChaosPolynomial k) h,
    rankDivergence_coeFn (firstChaosPolynomial h) k,
    firstChaosPolynomial_coeFn h,firstChaosPolynomial_coeFn k,
    firstChaosPolynomial_derivative_coeFn h,firstChaosPolynomial_derivative_coeFn k]
    with ω h1 h2 hh hk hdh hdk
  rw [h1,h2,hh,hk,hdh,hdk,real_inner_comm h k]
  ring

def skewField (h k : CoefficientSpace) : GaussianVectorL2 :=
  scalarTensor h (firstChaosEmbedding k)-scalarTensor k (firstChaosEmbedding h)

theorem skewField_divergence_zero (h k : CoefficientSpace) :
    (skewField h k,0) ∈ hilbertDivergence.graph := by
  have h1 := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (firstChaosPolynomial k) h)
  have h2 := LinearPMap.le_graph_of_le cylindricalDivergence_le_hilbertDivergence
    (cylindricalDivergence_rank_graph (firstChaosPolynomial h) k)
  rw [firstChaosPolynomial_eq_embedding] at h1 h2
  have hs := hilbertDivergence.graph.sub_mem h1 h2
  simpa only [Prod.mk_sub_mk, rankDivergence_linear_symmetric h k, sub_self, skewField] using hs

theorem skewField_norm_sq (h k : CoefficientSpace) :
    ‖skewField h k‖^2 = 2*(‖h‖^2*‖k‖^2-(inner ℝ h k)^2) := by
  have hn (a b : CoefficientSpace) :
      ‖scalarTensor a (firstChaosEmbedding b)‖^2 = ‖a‖^2*‖b‖^2 := by
    rw [← real_inner_self_eq_norm_sq,scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map,
      real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    ring
  have hi : inner ℝ (scalarTensor h (firstChaosEmbedding k))
      (scalarTensor k (firstChaosEmbedding h)) = (inner ℝ h k)^2 := by
    rw [scalarTensor_pair_inner,firstChaosEmbedding.inner_map_map,real_inner_comm h k]
    ring
  rw [skewField,norm_sub_sq_real,hn,hn,hi]
  ring

/-- A concrete nonzero divergence-free Gaussian polynomial field. -/
theorem gaussian_nonzero_divergence_kernel :
    ∃ u : GaussianVectorL2, u ≠ 0 ∧ (u,0) ∈ hilbertDivergence.graph := by
  let h : CoefficientSpace := lp.single 2 0 (1 : ℝ)
  let k : CoefficientSpace := lp.single 2 1 (1 : ℝ)
  have hh : ‖h‖^2=1 := by simp [h,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2)]
  have hk : ‖k‖^2=1 := by simp [k,lp.norm_single (by norm_num : (0 : ℝ≥0∞)<2)]
  have hi : inner ℝ h k=0 := by
    change inner ℝ (lp.single 2 0 (1 : ℝ) : CoefficientSpace)
      (lp.single 2 1 (1 : ℝ) : CoefficientSpace) = 0
    rw [lp.inner_single_left]
    simp [lp.single_apply,Pi.single_apply]
  refine ⟨skewField h k, ?_,skewField_divergence_zero h k⟩
  have he : ‖skewField h k‖^2=2 := by rw [skewField_norm_sq,hh,hk,hi]; norm_num
  intro hz
  rw [hz,norm_zero] at he
  norm_num at he

end OperatorDerivativeRewrite.Foundation.DivergenceKernelContrast
