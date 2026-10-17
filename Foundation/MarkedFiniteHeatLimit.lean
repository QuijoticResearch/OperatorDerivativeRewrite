import Foundation.MarkedIndependentIncrements
import Foundation.ComplexRootPoissonHeatLimit
import Foundation.HigherHeatCylinderFourier

/-! Finite-dimensional holomorphic process limits, with actual signed cylinder targets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.MarkedFiniteHeatLimit
open MarkedRootRenewalProcess (probability)
open MarkedHolomorphicExponential MarkedTwoTimeHolomorphicTransform MarkedIndependentIncrements
open ComplexRootHeatTransformLimit

theorem scaled_increment_transform {n : ℕ} (m : ℕ) (t : Fin (n+1) → ℝ≥0)
    (ht : Monotone t) (ξ : Fin n → ℝ) :
    (∫ ω, ∏ j : Fin n, futurePhase (amplitude 1 m) (ξ j)
      ((m : ℝ≥0)*t j.castSucc) ((m : ℝ≥0)*t j.succ) ω ∂probability) =
      ∏ j : Fin n, Complex.exp (((m : ℝ≥0)*(t j.succ-t j.castSucc) : ℝ≥0)*
        symbol (amplitude 1 m) (ξ j)) := by
  rw [increment_transform _ _ (fun i j hij =>
    mul_le_mul_of_nonneg_left (ht hij) (zero_le : 0 ≤ (m : ℝ≥0)))]
  simp only [← mul_tsub]

theorem finite_increment_heat_limit {n : ℕ} (t : Fin (n+1) → ℝ≥0)
    (ht : Monotone t) (ξ : Fin n → ℝ) :
    Tendsto (fun m : ℕ => ∫ ω, ∏ j : Fin n, futurePhase (amplitude 1 m) (ξ j)
      ((m : ℝ≥0)*t j.castSucc) ((m : ℝ≥0)*t j.succ) ω ∂probability) atTop
      (𝓝 (∏ j : Fin n, (Real.exp (-((t j.succ-t j.castSucc : ℝ≥0) : ℝ)*(ξ j)^4) : ℂ))) := by
  have hs (j : Fin n) :
      Tendsto (fun m : ℕ => Complex.exp
        ((((m : ℝ≥0)*(t j.succ-t j.castSucc) : ℝ≥0) : ℂ)*symbol (amplitude 1 m) (ξ j))) atTop
        (𝓝 (Real.exp (-((t j.succ-t j.castSucc : ℝ≥0) : ℝ)*(ξ j)^4) : ℂ)) := by
    simpa only [ComplexRootPoissonTransform.transform, symbol] using
      ComplexRootPoissonHeatLimit.rate_scaled_transform_limit (t j.succ-t j.castSucc) (ξ j)
  have hp := tendsto_finsetProd (Finset.univ : Finset (Fin n)) (fun j _ => hs j)
  simpa only [← scaled_increment_transform _ t ht ξ] using hp

theorem finite_operator_heat_limit {n : ℕ} (t : Fin (n+1) → ℝ≥0)
    (ht : Monotone t) (ξ : Fin n → ℝ) :
    Tendsto (fun m : ℕ => ∫ ω, ∏ j : Fin n, futurePhase (amplitude 1 m) (2*Real.pi*ξ j)
      ((m : ℝ≥0)*t j.castSucc) ((m : ℝ≥0)*t j.succ) ω ∂probability) atTop
      (𝓝 (∏ j : Fin n, HigherHeatL2.symbol 2 (t j.succ-t j.castSucc) (ξ j))) := by
  simpa only [HigherHeatL2.symbol, show 2*2=4 from rfl] using
    finite_increment_heat_limit t ht (fun j => 2*Real.pi*ξ j)

theorem signed_cylinder_heat_limit {n : ℕ} {κ : Type*} [Fintype κ]
    (t : Fin (n+1) → ℝ≥0) (ht : Monotone t)
    (hdt : ∀ j : Fin n, 0 < t j.succ-t j.castSucc)
    (B : κ → Fin n → ℝ) (ξ : κ → ℝ) :
    Tendsto (fun m : ℕ => ∫ ω, ∏ j : Fin n,
      futurePhase (amplitude 1 m) (2*Real.pi*HigherHeatCylinderFourier.dualImage B ξ j)
        ((m : ℝ≥0)*t j.castSucc) ((m : ℝ≥0)*t j.succ) ω ∂probability) atTop
      (𝓝 (HigherHeatCylinderFourier.cylinderFourier 2 (by decide)
        (fun j : Fin n => t j.succ-t j.castSucc) hdt B ξ)) := by
  rw [HigherHeatCylinderFourier.cylinderFourier_eq]
  exact finite_operator_heat_limit t ht (HigherHeatCylinderFourier.dualImage B ξ)

variable {n : ℕ} {κ : Type*} [Fintype κ]

def configuration (a : ℝ) (t : Fin (n+1) → ℝ≥0) (B : κ → Fin n → ℝ)
    (ω : MarkedRootRenewalProcess.StateSample) (i : κ) : ℂ :=
  ∑ j : Fin n, (B i j : ℂ)*MarkedConditionalPolynomial.increment a (t j.castSucc) (t j.succ) ω

theorem configuration_measurable (a : ℝ) (t : Fin (n+1) → ℝ≥0) (B : κ → Fin n → ℝ) :
    Measurable (configuration a t B) :=
  Measurable.of_eval fun i => Finset.measurable_sum _ fun j _ =>
    (MarkedConditionalPolynomial.increment_measurable a (t j.castSucc) (t j.succ)).const_mul
      (B i j : ℂ)

def configurationLaw (a : ℝ) (t : Fin (n+1) → ℝ≥0) (B : κ → Fin n → ℝ) : Measure (κ → ℂ) :=
  probability.map (configuration a t B)

instance configurationLaw_isProbability (a : ℝ) (t : Fin (n+1) → ℝ≥0)
    (B : κ → Fin n → ℝ) : IsProbabilityMeasure (configurationLaw a t B) where
  measure_univ := by
    rw [configurationLaw, Measure.map_apply (configuration_measurable a t B) MeasurableSet.univ,
      Set.preimage_univ, measure_univ]

theorem configuration_phase_factor (a : ℝ) (t : Fin (n+1) → ℝ≥0)
    (B : κ → Fin n → ℝ) (ξ : κ → ℝ) (ω : MarkedRootRenewalProcess.StateSample) :
    Complex.exp (Complex.I*(2*Real.pi : ℝ)*(∑ i, (ξ i : ℂ)*configuration a t B ω i)) =
      ∏ j : Fin n, futurePhase a (2*Real.pi*HigherHeatCylinderFourier.dualImage B ξ j)
        (t j.castSucc) (t j.succ) ω := by
  unfold configuration futurePhase HigherHeatCylinderFourier.dualImage
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem configuration_phase_integrable (a : ℝ) (t : Fin (n+1) → ℝ≥0) (ht : Monotone t)
    (B : κ → Fin n → ℝ) (ξ : κ → ℝ) :
    Integrable (fun z : κ → ℂ => Complex.exp (Complex.I*(2*Real.pi : ℝ)*
      (∑ i, (ξ i : ℂ)*z i))) (configurationLaw a t B) := by
  have hm : Measurable (fun z : κ → ℂ => Complex.exp (Complex.I*(2*Real.pi : ℝ)*
      (∑ i, (ξ i : ℂ)*z i))) := by fun_prop
  apply (integrable_map_measure hm.aestronglyMeasurable
    (configuration_measurable a t B).aemeasurable).mpr
  change Integrable (fun ω => Complex.exp (Complex.I*(2*Real.pi : ℝ)*
    (∑ i, (ξ i : ℂ)*configuration a t B ω i))) probability
  simpa only [configuration_phase_factor] using increment_product_integrable a t ht
    (fun j => 2*Real.pi*HigherHeatCylinderFourier.dualImage B ξ j)

theorem configurationLaw_heat_limit (t : Fin (n+1) → ℝ≥0) (ht : Monotone t)
    (hdt : ∀ j : Fin n, 0 < t j.succ-t j.castSucc)
    (B : κ → Fin n → ℝ) (ξ : κ → ℝ) :
    Tendsto (fun m : ℕ => ∫ z : κ → ℂ,
      Complex.exp (Complex.I*(2*Real.pi : ℝ)*(∑ i, (ξ i : ℂ)*z i))
        ∂configurationLaw (amplitude 1 m) (fun j => (m : ℝ≥0)*t j) B) atTop
      (𝓝 (HigherHeatCylinderFourier.cylinderFourier 2 (by decide)
        (fun j : Fin n => t j.succ-t j.castSucc) hdt B ξ)) := by
  have hm : Measurable (fun z : κ → ℂ => Complex.exp (Complex.I*(2*Real.pi : ℝ)*
      (∑ i, (ξ i : ℂ)*z i))) := by fun_prop
  have he (m : ℕ) : (∫ z : κ → ℂ,
      Complex.exp (Complex.I*(2*Real.pi : ℝ)*(∑ i, (ξ i : ℂ)*z i))
        ∂configurationLaw (amplitude 1 m) (fun j => (m : ℝ≥0)*t j) B) =
      ∫ ω, ∏ j : Fin n, futurePhase (amplitude 1 m)
        (2*Real.pi*HigherHeatCylinderFourier.dualImage B ξ j)
        ((m : ℝ≥0)*t j.castSucc) ((m : ℝ≥0)*t j.succ) ω ∂probability := by
    rw [configurationLaw, integral_map (configuration_measurable _ _ B).aemeasurable
      hm.aestronglyMeasurable]
    simp only [configuration_phase_factor]
  simpa only [he] using signed_cylinder_heat_limit t ht hdt B ξ

end OperatorDerivativeRewrite.Foundation.MarkedFiniteHeatLimit
