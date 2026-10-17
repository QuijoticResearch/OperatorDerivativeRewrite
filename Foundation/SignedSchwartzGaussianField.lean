import Foundation.EnergyResolventGaussianField
import Foundation.SignedSchwartzEnergyOperator
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Actual auxiliary Gaussian fields with the signed-marginal derivative-energy Green covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped SchwartzMap Topology NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzGaussianField
open SignedSchwartzL2Rigging SignedSchwartzClosedDerivative InfiniteGaussian

theorem marginal_secondCountable (K : 𝓢(ℝ, ℝ)) : SecondCountableTopology (H K) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
  infer_instance

attribute [local instance] marginal_secondCountable

def embedding (K : 𝓢(ℝ, ℝ)) : H K →L[ℝ] GaussianL2 :=
  EnergyResolventGaussianField.embedding (closedDerivative K) (closedDerivative_closed K)

def field (K : 𝓢(ℝ, ℝ)) (x : H K) : SampleSpace → ℝ := embedding K x

theorem field_measurable (K : 𝓢(ℝ, ℝ)) (x : H K) : Measurable (field K x) :=
  EnergyResolventGaussianField.field_measurable _ _ x

theorem field_gaussian (K : 𝓢(ℝ, ℝ)) : IsGaussianProcess (field K) gaussianProduct :=
  EnergyResolventGaussianField.field_gaussian _ _

theorem field_covariance (K : 𝓢(ℝ, ℝ)) (x y : H K) :
    cov[field K x, field K y; gaussianProduct] =
      inner ℝ x (SignedSchwartzEnergyResolvent.resolvent K y) :=
  EnergyResolventGaussianField.field_covariance _ _ x y

theorem field_centered (K : 𝓢(ℝ, ℝ)) (x : H K) :
    (∫ ω, field K x ω ∂gaussianProduct)=0 :=
  EnergyResolventGaussianField.field_centered _ _ x

theorem variance_positive (K : 𝓢(ℝ, ℝ)) (x : H K) (hx : x≠0) :
    0 < inner ℝ x (SignedSchwartzEnergyResolvent.resolvent K x) :=
  EnergyResolventGaussianField.variance_positive _ _ (closedDerivative_dense_domain K) x hx

theorem embedding_continuous (K : 𝓢(ℝ, ℝ)) : Continuous (embedding K) := (embedding K).continuous

def sourceDerivative (K : 𝓢(ℝ, ℝ)) (x : H K) : GaussianVectorL2 :=
  EnergyResolventGaussianField.sourceDerivative (closedDerivative K) (closedDerivative_closed K) x

theorem source_calculus (K : 𝓢(ℝ, ℝ)) (x : H K) :
    (embedding K x, sourceDerivative K x) ∈ closedCylindricalDerivative.graph ∧
      (sourceDerivative K x, embedding K x) ∈ hilbertDivergence.graph ∧
      GaussianDivergenceRecovery.recovery (embedding K x)=sourceDerivative K x :=
  ⟨EnergyResolventGaussianField.source_derivative_graph _ _ x,
    EnergyResolventGaussianField.source_divergence_graph _ _ x,
    EnergyResolventGaussianField.source_recovery _ _ x⟩

theorem green_covariance (K : 𝓢(ℝ, ℝ)) (x : H K)
    (u : (SignedSchwartzEnergyOperator.operator K).domain) :
    cov[field K x, field K ((u:H K)+SignedSchwartzEnergyOperator.operator K u); gaussianProduct] =
      inner ℝ x (u:H K) := by
  rw [field_covariance]
  have hr : SignedSchwartzEnergyResolvent.resolvent K
      ((u:H K)+SignedSchwartzEnergyOperator.operator K u)=(u:H K) := by
    obtain ⟨y,hy,hv⟩ := ClosedOperatorEnergyOperator.input_representation
      (closedDerivative K) (closedDerivative_closed K) (closedDerivative_dense_domain K) u
    change SignedSchwartzEnergyResolvent.resolvent K y=(u:H K) at hy
    change y-SignedSchwartzEnergyResolvent.resolvent K y=
      SignedSchwartzEnergyOperator.operator K u at hv
    have he : (u:H K)+SignedSchwartzEnergyOperator.operator K u=y := by
      rw [← hy, ← hv]
      abel
    rw [he]
    exact hy
  rw [hr]

def higherHeatField (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    H (HigherHeatSignedLaws.realKernel m hm t ht) → SampleSpace → ℝ :=
  field (HigherHeatSignedLaws.realKernel m hm t ht)

theorem higherHeatField_gaussian (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) :
    IsGaussianProcess (higherHeatField m hm t ht) gaussianProduct := field_gaussian _

end OperatorDerivativeRewrite.Foundation.SignedSchwartzGaussianField
