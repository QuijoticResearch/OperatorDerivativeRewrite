import Foundation.GaussianQuarticResidualCovariance

/-! Actual Gaussian finite-block quartic variances and the T1/T2 covariance
formula. This is a Gaussian reference identity, not an interacting entropy bound. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.GaussianQuarticBlockVariance
open InfiniteGaussian GaussianConditionalGraph GaussianWickConditionalProjection
open GaussianQuarticConditionalVariance GaussianQuarticResidualCovariance
set_option backward.isDefEq.respectTransparency false
variable {P I : Type*} [Fintype P]

def totalCov (u : P → CoefficientSpace) (p q : P) : ℝ := inner ℝ (u p) (u q)
def boundaryCov (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p q : P) : ℝ :=
  inner ℝ (sourceProjection h (u p)) (sourceProjection h (u q))
def interiorCov (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p q : P) : ℝ :=
  inner ℝ (u p-sourceProjection h (u p)) (u q-sourceProjection h (u q))
def totalDiag (u : P → CoefficientSpace) (p : P) : ℝ := ‖u p‖^2
def boundaryDiag (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p : P) : ℝ :=
  ‖sourceProjection h (u p)‖^2
def residualDiag (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p : P) : ℝ :=
  totalDiag u p-boundaryDiag h u p

def weighted (d e : P → ℝ) (M : P → P → ℝ) : ℝ := ∑ p, ∑ q, d p*e q*(M p q)^2
def T1 (M : P → P → ℝ) : ℝ := ∑ p, ∑ q, M p p*M q q*(M p q)^2
def T2 (M : P → P → ℝ) : ℝ := ∑ p, ∑ q, (M p q)^4

def block (u : P → CoefficientSpace) : GaussianL2 := (1/24 : ℝ) • ∑ p, centeredQuartic (u p)

theorem covariance_decomposition (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p q : P) :
    totalCov u p q=boundaryCov h u p q+interiorCov h u p q := by
  have he := GaussianCubicConditionalPrediction.residualCovariance_eq_inner h (u p) (u q)
  change totalCov u p q-boundaryCov h u p q=interiorCov h u p q at he
  linarith

theorem residualDiag_eq_interior (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p : P) :
    residualDiag h u p=interiorCov h u p p := by
  have he := covariance_decomposition h u p p
  simp only [totalCov,boundaryCov,interiorCov,real_inner_self_eq_norm_sq] at he ⊢
  unfold residualDiag totalDiag boundaryDiag
  linarith

theorem residualDiag_nonneg (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p : P) :
    0 ≤ residualDiag h u p := by
  rw [residualDiag_eq_interior]
  exact real_inner_self_nonneg

theorem block_mean (u : P → CoefficientSpace) : (∫ ω, block u ω ∂gaussianProduct)=0 := by
  rw [← gaussianOne_inner_eq_integral]
  simp only [block,real_inner_smul_right,inner_sum,gaussianOne_inner_eq_integral,
    centeredQuartic_mean,Finset.sum_const_zero,mul_zero]

theorem block_norm_sq (u : P → CoefficientSpace) :
    ‖block u‖^2=(72*T1 (totalCov u)+24*T2 (totalCov u))/576 := by
  have hc : (∑ p, ∑ q, inner ℝ (centeredQuartic (u p)) (centeredQuartic (u q)))=
      72*T1 (totalCov u)+24*T2 (totalCov u) := by
    unfold T1 T2 totalCov
    simp only [real_inner_self_eq_norm_sq,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [quartic_covariance]
    ring
  rw [← real_inner_self_eq_norm_sq]
  simp only [block,real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm,hc]
  ring

theorem block_prediction (h : I → CoefficientSpace) (u : P → CoefficientSpace) :
    conditionalProjection h (block u)=(1/24 : ℝ) • ∑ p, prediction h (u p) := by
  simp only [block,map_smul,map_sum,prediction]

theorem block_prediction_condExp (h : I → CoefficientSpace) (u : P → CoefficientSpace) :
    conditionalProjection h (block u) =ᵐ[gaussianProduct]
      gaussianProduct[block u | MeasurableSpace.comap (firstChaosFamily h) inferInstance] :=
  conditionalProjection_ae_condExp h (block u)

theorem block_prediction_norm_sq (h : I → CoefficientSpace) (u : P → CoefficientSpace) :
    ‖conditionalProjection h (block u)‖^2=
      (72*weighted (totalDiag u) (totalDiag u) (boundaryCov h u)+24*T2 (boundaryCov h u))/576 := by
  have hc : (∑ p, ∑ q, inner ℝ (prediction h (u p)) (prediction h (u q)))=
      72*weighted (totalDiag u) (totalDiag u) (boundaryCov h u)+24*T2 (boundaryCov h u) := by
    unfold weighted totalDiag T2 boundaryCov
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [prediction_covariance]
    ring
  rw [block_prediction,← real_inner_self_eq_norm_sq]
  simp only [real_inner_smul_left,real_inner_smul_right,sum_inner,inner_sum]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_comm,hc]
  ring

theorem weighted_add_left (d e f : P → ℝ) (M : P → P → ℝ) :
    weighted (d+e) f M=weighted d f M+weighted e f M := by
  simp only [weighted,Pi.add_apply,add_mul,Finset.sum_add_distrib]

theorem weighted_add_right (d e f : P → ℝ) (M : P → P → ℝ) :
    weighted d (e+f) M=weighted d e M+weighted d f M := by
  simp only [weighted,Pi.add_apply,mul_add,add_mul,Finset.sum_add_distrib]

theorem weighted_symmetric (d e : P → ℝ) (M : P → P → ℝ) (hM : ∀ p q, M p q=M q p) :
    weighted d e M=weighted e d M := by
  unfold weighted
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [hM q p]
  ring

theorem boundaryCov_symmetric (h : I → CoefficientSpace) (u : P → CoefficientSpace) (p q : P) :
    boundaryCov h u p q=boundaryCov h u q p := real_inner_comm _ _

theorem weighted_total_decomposition (h : I → CoefficientSpace) (u : P → CoefficientSpace) :
    weighted (totalDiag u) (totalDiag u) (boundaryCov h u)=
      weighted (boundaryDiag h u) (boundaryDiag h u) (boundaryCov h u)+
      weighted (residualDiag h u) (residualDiag h u) (boundaryCov h u)+
      2*weighted (boundaryDiag h u) (residualDiag h u) (boundaryCov h u) := by
  have he : totalDiag u=boundaryDiag h u+residualDiag h u := by
    funext p
    simp only [Pi.add_apply,residualDiag]
    ring
  rw [he,weighted_add_left,weighted_add_right,weighted_add_right]
  rw [weighted_symmetric (residualDiag h u) (boundaryDiag h u) _ (boundaryCov_symmetric h u)]
  ring

theorem boundary_T1 (h : I → CoefficientSpace) (u : P → CoefficientSpace) :
    weighted (boundaryDiag h u) (boundaryDiag h u) (boundaryCov h u)=T1 (boundaryCov h u) := by
  simp only [weighted,T1,boundaryDiag,boundaryCov,real_inner_self_eq_norm_sq]

/-- The printed three-term retained-variance formula holds for the actual Gaussian block. -/
theorem block_prediction_split (h : I → CoefficientSpace) (u : P → CoefficientSpace) :
    ‖conditionalProjection h (block u)‖^2=
      (72*T1 (boundaryCov h u)+24*T2 (boundaryCov h u))/576+
      (1/8 : ℝ)*weighted (residualDiag h u) (residualDiag h u) (boundaryCov h u)+
      (1/4 : ℝ)*weighted (boundaryDiag h u) (residualDiag h u) (boundaryCov h u) := by
  rw [block_prediction_norm_sq,weighted_total_decomposition,boundary_T1]
  ring

end OperatorDerivativeRewrite.Foundation.GaussianQuarticBlockVariance
