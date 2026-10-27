import Foundation.PhysicalHeatChainGamma
import Foundation.FiniteSchoenberg

/-!
# Finite-time Fourier Gamma from a physical heat chain

For a normalized covariance symbol `r`, the finite-time transform
`1 - exp (-t*r)` is again a covariance symbol. Its anchored Gamma kernel is
half of the actual character-increment covariance under the fixed-step heat
chain. The negative-symbol argument uses the verified finite Schoenberg
criterion; it proves positivity at each time, without asserting positive
Bakry curvature, a spectral gap, or a continuous-time path construction.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FourierCovarianceCriterion
open FiniteStableGamma.Core FiniteSchoenberg AnchoredCovariance
open FourierGammaNormalization
open scoped NNReal BigOperators

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatChain

def heatIncrementSymbol (r : Wave → ℝ≥0) (t : ℝ≥0) (k : Wave) : ℝ :=
  1 - Real.exp (-((t : ℝ) * (r k : ℝ)))

theorem heatIncrementSymbol_zero (r : Wave → ℝ≥0)
    (hr0 : r 0 = 0) (t : ℝ≥0) : heatIncrementSymbol r t 0 = 0 := by
  simp [heatIncrementSymbol, hr0]

theorem heatIncrementSymbol_even (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (t : ℝ≥0) (k : Wave) : heatIncrementSymbol r t (-k) = heatIncrementSymbol r t k := by
  have h0 : (fun j : Wave => (r j : ℝ)) 0 = 0 := by simp [hr0]
  have hp := (normalized_gamma_iff_covariance (fun j : Wave => (r j : ℝ)) h0).mpr hr
  have he := even_of_gamma_positive (fun j : Wave => (r j : ℝ)) h0 hp k
  simp [heatIncrementSymbol, he]

theorem heatIncrementSymbol_negative (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (t : ℝ≥0) :
    NegativeSymbol (heatIncrementSymbol r t) := by
  intro ι _ _ k c hc
  have hM : Matrix.PosSemidef (fun i j : ι =>
      Real.exp (-(t : ℝ) * (r (k j-k i) : ℝ))) :=
    heat_multiplier_psd_of_covariance (fun q => (r q : ℝ)) hr t t.property k
  have hE : 0 ≤ energy (fun i j : ι =>
      Real.exp (-(t : ℝ) * (r (k j-k i) : ℝ))) c := by
    simpa only [energy, dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
      hM.dotProduct_mulVec_nonneg c
  have hsum : (∑ i, ∑ j, c i * c j) = 0 := by
    rw [← Fintype.sum_mul_sum]
    rw [hc]
    ring
  have hid : energy (fun i j => heatIncrementSymbol r t (k j-k i)) c =
      -energy (fun i j : ι => Real.exp (-(t : ℝ) * (r (k j-k i) : ℝ))) c := by
    simp only [energy, heatIncrementSymbol, mul_sub, mul_one, Finset.sum_sub_distrib]
    simp only [← neg_mul]
    rw [hsum]
    ring
  rw [hid]
  exact neg_nonpos.mpr hE

theorem heatIncrementSymbol_covariance (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) :
    CovarianceSymbol (heatIncrementSymbol r t) := by
  exact (symbol_iff _ (heatIncrementSymbol_zero r hr0 t)
    (heatIncrementSymbol_even r hr hr0 t)).mpr
    (heatIncrementSymbol_negative r hr t)

theorem heatIncrementSymbol_kernel (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (t : ℝ≥0) (k l : Wave) :
    2 * kernel (heatIncrementSymbol r t) k l =
      Real.exp (-((t : ℝ) * (r (k-l) : ℝ))) -
      Real.exp (-((t : ℝ) * (r k : ℝ))) -
      Real.exp (-((t : ℝ) * (r l : ℝ))) + 1 := by
  have hs : l-k = -(k-l) := by abel
  simp only [kernel]
  rw [hs, heatIncrementSymbol_even r hr hr0 t (k-l)]
  simp only [heatIncrementSymbol]
  ring

theorem chainLaw_increment_pair_gamma (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ))) (hr0 : r 0 = 0)
    (t : ℝ≥0) (k l : Wave) :
    (∫ path, (UnitAddTorus.mFourier (-k) (path 1) - 1) *
      (UnitAddTorus.mFourier l (path 1) - 1)
      ∂chainLaw r hr hr0 t (0 : UnitAddTorus (Fin 3))) =
      (2 * kernel (heatIncrementSymbol r t) k l : ℂ) := by
  rw [chainLaw_increment_pair]
  exact_mod_cast (heatIncrementSymbol_kernel r hr hr0 t k l).symm

end OperatorDerivativeRewrite.Foundation.PhysicalHeatChain
