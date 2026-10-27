import Foundation.PhysicalHeatFiniteTimeCovariance
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# A genuine compound-Poisson heat law

Mix the verified physical heat probability laws at times `n * δ` against
Mathlib's genuine Poisson count law. This yields a probability measure on
the torus. Its Fourier character is `exp(-rate * (1 - exp(-δ*r(k))))`.
The positive transformed rate is a covariance symbol, and Fourier uniqueness
identifies the mixture with its physical heat law. Convolution in the Poisson
rate and the time-zero Dirac law follow. This is a fixed-time probability-law
construction, not a cadlag process or a filtration theorem.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open PhysicalHeatConvolution
open PhysicalHeatChain
open PhysicalHeatLawUnique
open MeasureTheory ProbabilityTheory AddCircle
open scoped NNReal ENNReal

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatCompoundPoisson

def poissonWeight (rate : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(rate : ℝ)) * (rate : ℝ)^n / n.factorial

theorem poissonWeight_nonneg (rate : ℝ≥0) (n : ℕ) :
    0 ≤ poissonWeight rate n := by
  unfold poissonWeight
  positivity

def compoundHeatLaw (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) : Measure (UnitAddTorus (Fin 3)) :=
  (poissonMeasure rate).bind (fun n =>
    (heatLaw r hr hr0 ((n : ℝ≥0) * δ) : Measure (UnitAddTorus (Fin 3))))

instance compoundHeatLaw_isProbability (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) : IsProbabilityMeasure (compoundHeatLaw r hr hr0 δ rate) := by
  constructor
  rw [compoundHeatLaw, Measure.bind_apply MeasurableSet.univ
    (measurable_of_countable _).aemeasurable]
  simp

theorem compoundHeatLaw_sum (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) :
    compoundHeatLaw r hr hr0 δ rate =
      Measure.sum (fun n => ENNReal.ofReal (poissonWeight rate n) •
        (heatLaw r hr hr0 ((n : ℝ≥0) * δ) : Measure (UnitAddTorus (Fin 3)))) := by
  unfold compoundHeatLaw poissonMeasure
  rw [Measure.bind_sum _ _ (measurable_of_countable _).aemeasurable]
  congr 1
  funext n
  rw [Measure.bind_smul _ _ (measurable_of_countable _).aemeasurable,
    Measure.dirac_bind (measurable_of_countable _)]
  rfl

theorem compoundHeatLaw_character_tsum (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) (k : Wave) :
    (∫ x, UnitAddTorus.mFourier (-k) x ∂compoundHeatLaw r hr hr0 δ rate) =
      ∑' n : ℕ, (poissonWeight rate n : ℂ) *
        (Real.exp (-(((n : ℝ≥0) * δ : ℝ) * (r k : ℝ))) : ℂ) := by
  have hi : Integrable (fun x => UnitAddTorus.mFourier (-k) x)
      (compoundHeatLaw r hr hr0 δ rate) :=
    (UnitAddTorus.mFourier (-k)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [compoundHeatLaw_sum] at hi ⊢
  rw [integral_sum_measure hi]
  simp_rw [integral_smul_measure]
  simp_rw [ENNReal.toReal_ofReal (poissonWeight_nonneg rate _)]
  simp_rw [heatLaw_character]
  simp only [Complex.real_smul]
  simp only [NNReal.coe_mul]

private theorem poisson_exponential_series (rate : ℝ≥0) (a : ℝ) :
    (∑' n : ℕ, (poissonWeight rate n : ℂ) *
      (Real.exp (-((n : ℝ) * a)) : ℂ)) =
      (Real.exp (-(rate : ℝ) * (1 - Real.exp (-a))) : ℂ) := by
  let q : ℝ := Real.exp (-a)
  have hterm (n : ℕ) :
      (poissonWeight rate n : ℂ) * (Real.exp (-((n : ℝ) * a)) : ℂ) =
        (Real.exp (-(rate : ℝ)) : ℂ) *
          (((rate : ℝ) * q : ℝ) : ℂ)^n / (n.factorial : ℂ) := by
    have he : Real.exp (-((n : ℝ) * a)) = q^n := by
      rw [show -((n : ℝ) * a) = (n : ℝ) * (-a) by ring,
        Real.exp_nat_mul]
    rw [he]
    simp only [poissonWeight, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_div]
    dsimp [q]
    ring
  calc
    _ = (Real.exp (-(rate : ℝ)) : ℂ) *
        (∑' n : ℕ, ((((rate : ℝ) * q : ℝ) : ℂ)^n / (n.factorial : ℂ))) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [hterm]
      ring
    _ = (Real.exp (-(rate : ℝ)) : ℂ) *
        Complex.exp (((rate : ℝ) * q : ℝ) : ℂ) := by
      congr 1
      rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
    _ = _ := by
      rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 1
      dsimp [q]
      ring

theorem compoundHeatLaw_character (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) (k : Wave) :
    (∫ x, UnitAddTorus.mFourier (-k) x ∂compoundHeatLaw r hr hr0 δ rate) =
      (Real.exp (-((rate : ℝ) * heatIncrementSymbol r δ k)) : ℂ) := by
  rw [compoundHeatLaw_character_tsum]
  convert poisson_exponential_series rate ((δ : ℝ) * (r k : ℝ)) using 1
  · congr 1
    funext n
    congr 1
    congr 1
    simp only [NNReal.coe_natCast]
    ring
  · simp only [heatIncrementSymbol]
    ring

def jumpRate (r : Wave → ℝ≥0) (δ : ℝ≥0) (k : Wave) : ℝ≥0 :=
  ⟨heatIncrementSymbol r δ k, by
    unfold heatIncrementSymbol
    have h : Real.exp (-((δ : ℝ) * (r k : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    linarith⟩

theorem jumpRate_coe (r : Wave → ℝ≥0) (δ : ℝ≥0) (k : Wave) :
    (jumpRate r δ k : ℝ) = heatIncrementSymbol r δ k := rfl

theorem jumpRate_zero (r : Wave → ℝ≥0) (hr0 : r 0 = 0) (δ : ℝ≥0) :
    jumpRate r δ 0 = 0 := by
  apply NNReal.coe_injective
  rw [jumpRate_coe, heatIncrementSymbol_zero r hr0 δ]
  rfl

theorem jumpRate_covariance (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ : ℝ≥0) : CovarianceSymbol (fun k => (jumpRate r δ k : ℝ)) := by
  simpa only [jumpRate_coe] using heatIncrementSymbol_covariance r hr hr0 δ

theorem compoundHeatLaw_eq_heatLaw (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ rate : ℝ≥0) :
    compoundHeatLaw r hr hr0 δ rate =
      (heatLaw (jumpRate r δ) (jumpRate_covariance r hr hr0 δ)
        (jumpRate_zero r hr0 δ) rate : Measure (UnitAddTorus (Fin 3))) := by
  let μ : ProbabilityMeasure (UnitAddTorus (Fin 3)) :=
    (compoundHeatLaw r hr hr0 δ rate).toProbabilityMeasure
  have hμ (k : Wave) :
      (∫ x, UnitAddTorus.mFourier (-k) x
        ∂(μ : Measure (UnitAddTorus (Fin 3)))) =
        (Real.exp (-((rate : ℝ) * (jumpRate r δ k : ℝ))) : ℂ) := by
    change (∫ x, UnitAddTorus.mFourier (-k) x
      ∂compoundHeatLaw r hr hr0 δ rate) = _
    rw [compoundHeatLaw_character]
    rfl
  have he := physical_heat_law_unique (jumpRate r δ) rate μ
    (heatLaw (jumpRate r δ) (jumpRate_covariance r hr hr0 δ)
      (jumpRate_zero r hr0 δ) rate) hμ
    (heatLaw_character (jumpRate r δ) (jumpRate_covariance r hr hr0 δ)
      (jumpRate_zero r hr0 δ) rate)
  exact congrArg (fun q : ProbabilityMeasure (UnitAddTorus (Fin 3)) =>
    (q : Measure (UnitAddTorus (Fin 3)))) he

theorem compoundHeatLaw_conv (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ s t : ℝ≥0) :
    compoundHeatLaw r hr hr0 δ s ∗ compoundHeatLaw r hr hr0 δ t =
      compoundHeatLaw r hr hr0 δ (s+t) := by
  let hcr := jumpRate_covariance r hr hr0 δ
  let h0 := jumpRate_zero r hr0 δ
  calc
    _ = (heatLaw (jumpRate r δ) hcr h0 s : Measure (UnitAddTorus (Fin 3))) ∗
        (heatLaw (jumpRate r δ) hcr h0 t : Measure (UnitAddTorus (Fin 3))) := by
      rw [compoundHeatLaw_eq_heatLaw, compoundHeatLaw_eq_heatLaw]
    _ = (heatLaw (jumpRate r δ) hcr h0 (s+t) :
        Measure (UnitAddTorus (Fin 3))) := heatLaw_conv _ hcr h0 s t
    _ = _ := (compoundHeatLaw_eq_heatLaw r hr hr0 δ (s+t)).symm

theorem compoundHeatLaw_zero (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (δ : ℝ≥0) :
    compoundHeatLaw r hr hr0 δ 0 = Measure.dirac 0 := by
  rw [compoundHeatLaw_eq_heatLaw]
  exact heatLaw_zero (jumpRate r δ) (jumpRate_covariance r hr hr0 δ)
    (jumpRate_zero r hr0 δ)

end OperatorDerivativeRewrite.Foundation.PhysicalHeatCompoundPoisson
