import Foundation.GaussianMultitimeRepresentation
import Foundation.GaussianQuadraticCylinders

/-! Full predictable representation for the RAW Brownian-generated L² space.
The ambient Gaussian L² space is not asserted to be Brownian generated.
The independently defined predictable space and its previously constructed integral are unchanged. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianBrownianPRP
open InfiniteGaussian GaussianPredictableFull GaussianPredictableAdjoint
open GaussianBrownianGeneratedSpace GaussianTerminalRepresentation GaussianMultitimeRepresentation

theorem centered_brownianL2_mem_range (F : GaussianL2) (hF : F ∈ brownianL2) :
    centering F ∈ itoIntegral.toLinearMap.range := by
  have h : brownianL2 ≤ itoIntegral.toLinearMap.range.comap centering.toLinearMap := by
    rw [← brownianPolynomial_closure]
    apply Submodule.topologicalClosure_minimal
    · rintro F ⟨p, rfl⟩
      exact centered_brownianPolynomial_mem_range p
    · exact integralRange_isClosed.preimage centering.continuous
  exact h hF

/-- The exact range, including the raw generated sigma-algebra and centering condition. -/
theorem integralRange_eq_centeredBrownianL2 :
    itoIntegral.toLinearMap.range = centeredBrownianL2 := by
  apply le_antisymm integralRange_le_centeredBrownianL2
  intro F hF
  obtain ⟨hm, h0⟩ := (mem_centeredBrownianL2_iff F).mp hF
  have h := centered_brownianL2_mem_range F hm
  simpa only [centering_apply, h0, zero_smul, sub_zero] using h

theorem predictableAdjoint_centering (F : GaussianL2) :
    predictableAdjoint (centering F) = predictableAdjoint F := by
  rw [centering_apply, map_sub, GaussianQuadraticCylinders.predictableAdjoint_constant, sub_zero]

/-- The unique representer is the genuine bounded Hilbert adjoint of J. -/
theorem brownian_representation (F : GaussianL2) (hF : F ∈ brownianL2) :
    itoIntegral (predictableAdjoint F) =
      F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  obtain ⟨U, hU⟩ := centered_brownianL2_mem_range F hF
  change itoIntegral U = centering F at hU
  rw [← centering_apply, ← predictableAdjoint_centering, ← hU, predictableAdjoint_integral]

theorem brownian_representation_exists_unique (F : GaussianL2) (hF : F ∈ brownianL2) :
    ∃! U : fullPredictable,
      itoIntegral U = F - (∫ ω, F ω ∂gaussianProduct) • gaussianOne := by
  refine ⟨predictableAdjoint F, brownian_representation F hF, ?_⟩
  intro U hU
  exact itoIntegral.injective (hU.trans (brownian_representation F hF).symm)

theorem centered_representation_exists_unique (F : GaussianL2)
    (hF : AEStronglyMeasurable[brownianSigma] F gaussianProduct)
    (h0 : (∫ ω, F ω ∂gaussianProduct) = 0) :
    ∃! U : fullPredictable, itoIntegral U = F := by
  simpa only [h0, zero_smul, sub_zero] using brownian_representation_exists_unique F hF

/-- Clark--Ocone requires both Brownian measurability and membership in the actual closed
Malliavin derivative domain. PRP above does not require the latter. -/
theorem clark_ocone (F : closedCylindricalDerivative.domain)
    (hF : (F : GaussianL2) ∈ brownianL2) :
    (F : GaussianL2) - (∫ ω, (F : GaussianL2) ω ∂gaussianProduct) • gaussianOne =
      itoIntegral (predictableProjection (closedCylindricalDerivative F)) := by
  rw [← predictableAdjoint_eq_projected_derivative]
  exact (brownian_representation F hF).symm

theorem clark_ocone_representer_unique (F : closedCylindricalDerivative.domain)
    (hF : (F : GaussianL2) ∈ brownianL2) (U : fullPredictable)
    (hU : itoIntegral U = (F : GaussianL2) -
      (∫ ω, (F : GaussianL2) ω ∂gaussianProduct) • gaussianOne) :
    U = predictableProjection (closedCylindricalDerivative F) :=
  itoIntegral.injective (hU.trans (clark_ocone F hF))

theorem multitime_representer_agrees {ι : Type*} [Fintype ι]
    (r : ι → ℝ≥0) (p : MvPolynomial ι ℝ) :
    multitimePolynomialIntegrand r p =
      predictableAdjoint (GaussianTimeDivergence.pastCoefficient r p : GaussianL2) :=
  predictableAdjoint_centering _

end OperatorDerivativeRewrite.Foundation.GaussianBrownianPRP
