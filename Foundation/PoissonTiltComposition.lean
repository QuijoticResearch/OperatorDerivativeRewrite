import Foundation.PoissonExponentialTilt

/-! Actual Poisson tilts compose, while their ordered relative entropy
retains information that a symmetric square-root density kernel cannot. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.PoissonTiltComposition
open PoissonDifferenceCore PoissonExponentialTilt

theorem tiltedRate_add (rate : ℝ≥0) (θ η : ℝ) :
    tiltedRate (tiltedRate rate θ) η=tiltedRate rate (θ+η) := by
  apply NNReal.coe_injective
  change ((rate : ℝ)*Real.exp θ)*Real.exp η=(rate : ℝ)*Real.exp (θ+η)
  rw [Real.exp_add]
  ring

theorem tiltedRate_zero (rate : ℝ≥0) : tiltedRate rate 0=rate := by
  apply NNReal.coe_injective
  change (rate : ℝ)*Real.exp 0=(rate : ℝ)
  simp

theorem tiltedRate_inverse (rate : ℝ≥0) (θ : ℝ) :
    tiltedRate (tiltedRate rate θ) (-θ)=rate := by rw [tiltedRate_add,add_neg_cancel,tiltedRate_zero]

theorem density_cocycle (rate : ℝ≥0) (θ η : ℝ) (n : ℕ) :
    density rate (θ+η) n=density rate θ n*density (tiltedRate rate θ) η n := by
  rw [density,density,density,← Real.exp_add]
  change Real.exp ((θ+η)*(n : ℝ)-(rate : ℝ)*(Real.exp (θ+η)-1))=
    Real.exp ((θ*(n : ℝ)-(rate : ℝ)*(Real.exp θ-1))+
      (η*(n : ℝ)-((rate : ℝ)*Real.exp θ)*(Real.exp η-1)))
  rw [Real.exp_add θ η]
  congr 1
  ring

def relativeEntropy (rate : ℝ≥0) (θ : ℝ) : ℝ :=
  ∫ n, density rate θ n*Real.log (density rate θ n) ∂poissonLaw rate

theorem relativeEntropy_formula (rate : ℝ≥0) (θ : ℝ) :
    relativeEntropy rate θ=(rate : ℝ)*(θ*Real.exp θ-Real.exp θ+1) := relative_entropy rate θ

theorem reverse_relativeEntropy (rate : ℝ≥0) (θ : ℝ) :
    relativeEntropy (tiltedRate rate θ) (-θ)=(rate : ℝ)*(Real.exp θ-θ-1) := by
  rw [relativeEntropy_formula]
  change ((rate : ℝ)*Real.exp θ)*((-θ)*Real.exp (-θ)-Real.exp (-θ)+1)=_
  rw [Real.exp_neg]
  field_simp
  ring

theorem exact_entropy_asymmetry (rate : ℝ≥0) :
    relativeEntropy rate 2-relativeEntropy (tiltedRate rate 2) (-2)=4*(rate : ℝ) := by
  rw [relativeEntropy_formula,reverse_relativeEntropy]
  ring

theorem relativeEntropy_not_symmetric (rate : ℝ≥0) (hr : 0<rate) :
    relativeEntropy rate 2≠relativeEntropy (tiltedRate rate 2) (-2) := by
  intro he
  have hh := exact_entropy_asymmetry rate
  rw [he,sub_self] at hh
  have hp : (0 : ℝ)<rate := hr
  nlinarith

end OperatorDerivativeRewrite.Foundation.PoissonTiltComposition
