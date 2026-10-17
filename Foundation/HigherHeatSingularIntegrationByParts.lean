import Foundation.SignedDensityL1Transport
import Foundation.HigherHeatTemperedSemigroup

/-! Actual all-order signed integration by parts on Schwartz tests and dual time consistency. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSingularIntegrationByParts
open SignedAbsoluteIntegration SignedSchwartzHigherWeights HigherHeatSpatialGenerator

theorem schwartz_weight_integrable (n : ℕ) (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    Integrable (fun x : ℝ => (weight n K x:ℂ)*g x) (absoluteDensity volume K) := by
  apply (SignedDensityL1Transport.integrable_iff volume K (numerator n K) (weight n K)
    K.continuous.measurable (numerator n K).continuous.measurable
    (weight_measurable n K) (weight_cancel n K) g g.continuous.measurable).mpr
  exact SignedSchwartzLogDerivative.test_absolute_integrable (numerator n K) g

theorem schwartz_weight_integral (n : ℕ) (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    (∫ᵛ x : ℝ, (weight n K x:ℂ)*g x ∂<•volume.withDensityᵥ (K:ℝ → ℝ)) =
      (∫ x : ℝ, g x*(numerator n K x:ℂ)) := by
  rw [SignedDensityL1Transport.signed_integral_eq volume K (numerator n K) (weight n K)
    K.integrable (numerator n K).integrable K.continuous.measurable
    (numerator n K).continuous.measurable (weight_measurable n K) (weight_cancel n K)
    g g.continuous.measurable
    (SignedSchwartzLogDerivative.test_absolute_integrable (numerator n K) g),
    integral_density volume (numerator n K) (numerator n K).integrable
      (numerator n K).continuous.measurable g
      (SignedSchwartzLogDerivative.test_absolute_integrable (numerator n K) g)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp only; rw [Complex.real_smul, mul_comm]

theorem numerator_test (n : ℕ) (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, g x*(numerator n K x:ℂ)) =
      (∫ x : ℝ, jet n g x*(K x:ℂ)) / (n.factorial:ℂ) := by
  let F := K.postcompCLM Complex.ofRealCLM
  have hn (x : ℝ) : (numerator n K x:ℂ) =
      ((-1:ℂ)^n/(n.factorial:ℂ))*jet n F x := by
    simp only [numerator, SchwartzMap.smul_apply, smul_eq_mul]
    push_cast
    rw [realJet_complexify]
  have hi : (∫ x : ℝ, g x*jet n F x) =
      (-1:ℂ)^n*(∫ x : ℝ, jet n g x*F x) := by
    calc
      _ = ∫ x : ℝ, jet n F x*g x := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
      _ = (-1:ℂ)^n*(∫ x : ℝ, F x*jet n g x) := HigherHeatSchwartzJets.integral_jet_mul n F g
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun x => mul_comm _ _
  have hs : (-1:ℂ)^n*(-1:ℂ)^n=1 := by rw [← mul_pow]; norm_num
  calc
    _ = ((-1:ℂ)^n/(n.factorial:ℂ)) * (∫ x : ℝ, g x*jet n F x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by dsimp only; rw [hn]; ring
    _ = (∫ x : ℝ, jet n g x*F x) / (n.factorial:ℂ) := by
      rw [hi]
      calc
        _ = ((-1:ℂ)^n*(-1:ℂ)^n)*
            ((∫ x : ℝ, jet n g x*F x) / (n.factorial:ℂ)) := by ring
        _ = _ := by rw [hs, one_mul]
    _ = _ := rfl

theorem all_order_signed_ibp (n : ℕ) (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) :
    (∫ᵛ x : ℝ, (weight n K x:ℂ)*g x ∂<•volume.withDensityᵥ (K:ℝ → ℝ)) =
      (∫ᵛ x : ℝ, jet n g x ∂<•volume.withDensityᵥ (K:ℝ → ℝ)) / (n.factorial:ℂ) := by
  rw [schwartz_weight_integral, numerator_test,
    integral_density volume K K.integrable K.continuous.measurable (jet n g)
      (SignedSchwartzLogDerivative.test_absolute_integrable K (jet n g))]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by dsimp only; rw [Complex.real_smul, mul_comm]

theorem higher_heat_all_order (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (g : 𝓢(ℝ,ℂ)) :
    (∫ᵛ x : ℝ, (weight n (HigherHeatSignedLaws.realKernel m hm t ht) x:ℂ)*g x
      ∂<•HigherHeatSignedLaws.law m hm t ht) =
      (∫ᵛ x : ℝ, jet n g x ∂<•HigherHeatSignedLaws.law m hm t ht) / (n.factorial:ℂ) :=
  all_order_signed_ibp n _ g

theorem quartic_realized_weight (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (g : 𝓢(ℝ,ℂ)) :
    (∫ᵛ x : ℝ, (weight n (HigherHeatSignedLaws.realKernel 2 (by norm_num) t ht) x:ℂ)*g x
      ∂<•HigherHeatSignedLaws.law 2 (by norm_num) t ht) =
      QuarticDualDistributions.realized n t g := by
  rw [higher_heat_all_order, QuarticDualDistributions.realized_apply,
    ← HigherHeatSchwartzCalculus.mean_eq_signed_integral 2 (by norm_num) t ht (jet n g)]

theorem time_consistent_weights (s T : ℝ≥0) (hT : 0 < T) (n : ℕ) (g : 𝓢(ℝ,ℂ)) :
    (∫ᵛ x : ℝ, (weight n (HigherHeatSignedLaws.realKernel 2 (by norm_num) T hT) x:ℂ)*
      HigherHeatSchwartzSemigroup.evolve 2 (by norm_num) s g x
      ∂<•HigherHeatSignedLaws.law 2 (by norm_num) T hT) =
      (∫ᵛ x : ℝ, (weight n (HigherHeatSignedLaws.realKernel 2 (by norm_num) (s+T)
        (by positivity)) x:ℂ)*g x
        ∂<•HigherHeatSignedLaws.law 2 (by norm_num) (s+T) (by positivity)) := by
  rw [quartic_realized_weight, quartic_realized_weight]
  have h := congrArg (fun F : 𝓢'(ℝ,ℂ) => F g)
    (HigherHeatTemperedSemigroup.realized_propagation n s T)
  rw [HigherHeatTemperedSemigroup.transpose_apply] at h
  exact h

end OperatorDerivativeRewrite.Foundation.HigherHeatSingularIntegrationByParts
