import Foundation.HigherHeatPolynomialIto

/-! Actual signed Itô formula for every real terminal polynomial.
Its finitely many coefficient fields are genuine adapted L1 limits. -/
noncomputable section
open scoped NNReal Topology BigOperators
namespace OperatorDerivativeRewrite.Foundation.HigherHeatTerminalPolynomialIto
open Filter HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatWeakTimeAdjoint HigherHeatPairedDualCausality HigherHeatAllChannelNormalization
open HigherHeatPolynomialPredictableField HigherHeatPolynomialIto HigherHeatAdaptedStepDuality

def polynomialField (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (P : Polynomial ℝ)
    (q : ℕ) : Field timeMeasure :=
  ∑ N ∈ P.support, (P.coeff N*(N.choose (q+1):ℝ)) • powerField m hm T hT (N-(q+1))

theorem polynomial_field_mem (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) (q : ℕ) :
    polynomialField m hm T hT P q ∈ HigherHeatAdaptedIntegralClosure.space m hm T hT := by
  apply Submodule.sum_mem
  intro N _
  exact Submodule.smul_mem _ _ (field_mem m hm T hT (N-(q+1)))

theorem polynomial_fields_tendsto (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) (q : ℕ) :
    Tendsto (fun n => ∑ N ∈ P.support, (P.coeff N*(N.choose (q+1):ℝ)) •
      HigherHeatDyadicStepAgreement.adaptedField n m hm T hT (powerPast n (N-(q+1)))) atTop
        (𝓝 (polynomialField m hm T hT P q)) := by
  let : ContinuousAdd (Field timeMeasure) :=
    (inferInstance : IsTopologicalAddGroup (Field timeMeasure)).toContinuousAdd
  exact tendsto_finsetSum P.support (fun N _ =>
    (fields_tendsto m hm T hT (N-(q+1))).const_smul (P.coeff N*(N.choose (q+1):ℝ)))

theorem evaluation_difference (P : Polynomial ℝ) :
    Polynomial.aeval terminalCylinder P-Polynomial.aeval (0:Cylinder) P =
      ∑ N ∈ P.support, P.coeff N • (terminalCylinder^N-(0:Cylinder)^N) := by
  simp only [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
    Algebra.smul_def, mul_sub, Finset.sum_sub_distrib]

theorem polynomial_ito (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (P : Polynomial ℝ) :
    pairing m hm T hT (core (Polynomial.aeval terminalCylinder P-Polynomial.aeval (0:Cylinder) P)) =
      ∑ q ∈ Finset.range (2*m), channel m T q (polynomialField m hm T hT P q) := by
  calc
    _ = ∑ N ∈ P.support, P.coeff N •
        (∑ q ∈ Finset.range (2*m), N.choose (q+1) • channel m T q
          (powerField m hm T hT (N-(q+1)))) := by
      simp only [evaluation_difference, map_sum, map_smul, power_ito_channels m hm T hT]
    _ = _ := by
      simp only [Finset.smul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro q _
      simp only [polynomialField, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro N _
      apply ContinuousLinearMap.ext
      intro G
      simp only [smul_apply, nsmul_eq_mul, smul_eq_mul]
      ring

theorem actual_signed_identity (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (P : Polynomial ℝ) (G : Cylinder) :
    (((∑ q ∈ Finset.range (2*m), channel m T q (polynomialField m hm T hT P q)) (core G):ℝ):ℂ) =
      cylindricalExpectation m hm T hT
        ((Polynomial.aeval terminalCylinder P-Polynomial.aeval (0:Cylinder) P)*G) := by
  have he := congrArg (fun φ : Dual => (φ (core G):ℂ)) (polynomial_ito m hm T hT P)
  exact he.symm.trans (pairing_core_complex m hm T hT _ G)

end OperatorDerivativeRewrite.Foundation.HigherHeatTerminalPolynomialIto
