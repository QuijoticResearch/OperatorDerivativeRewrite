import Foundation.PureOrderAppellTail
import Foundation.SignedSchwartzHigherWeights

/-! Actual Schwartz-density and signed-L1 Appell coordinate duals at every even order. -/
noncomputable section
open Polynomial MeasureTheory
open scoped NNReal SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatAppellDuals
open PureOrderAppellCalculus PureOrderAppellExpansion HigherHeatSpatialGenerator
open SchwartzPolynomialPairing

def density (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) : 𝓢(ℝ,ℂ) :=
  ((-1:ℂ)^n / (n.factorial:ℂ)) •
    jet n (GaussianSchwartzKernel.evenKernel m hm t ht)

theorem density_polynomial_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (n : ℕ)
    (P : Polynomial ℝ) : Integrable (fun x : ℝ => ((P.eval x:ℝ):ℂ)*density m hm t ht n x) :=
  SchwartzPolynomialPairing.weighted_integrable P (density m hm t ht n)

theorem density_coordinate (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (P : Polynomial ℝ) :
    (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*density m hm t ht n x) =
      ((coordinate (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) n P : ℝ):ℂ) := by
  have hs : (-1:ℂ)^n * (-1:ℂ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1:ℂ)^n / (n.factorial:ℂ)) *
        (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*
          jet n (GaussianSchwartzKernel.evenKernel m hm t ht) x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp [density]; ring
    _ = _ := by
      rw [SchwartzPolynomialPairing.polynomial_jet_ibp,
        HigherHeatPolynomialRealization.complex_expectation,
        PureOrderAppellTail.actual_coordinate m hm t ht P n]
      push_cast
      calc
        _ = ((-1:ℂ)^n * (-1:ℂ)^n) *
            ((HigherHeatPolynomialRealization.kernelExpectation m hm t ht
              (derivative^[n] P):ℂ) / (n.factorial:ℂ)) := by ring
        _ = _ := by rw [hs, one_mul]


theorem density_biorthogonal (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (n k : ℕ) :
    (∫ x : ℝ, (((appell (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) k).eval x:ℝ):ℂ)*
      density m hm t ht n x) = if k=n then 1 else 0 := by
  rw [density_coordinate, coordinate_appell]
  split_ifs <;> norm_num

open SignedSchwartzHigherWeights

theorem numerator_eq_density (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (x : ℝ) :
    (numerator n (HigherHeatSignedLaws.realKernel m hm t ht) x:ℂ) =
      density m hm t ht n x := by
  have he : (HigherHeatSignedLaws.realKernel m hm t ht).postcompCLM Complex.ofRealCLM =
      GaussianSchwartzKernel.evenKernel m hm t ht := by
    ext y
    exact HigherHeatSignedLaws.realKernel_coe m hm t ht y
  simp only [numerator, density, smul_apply, smul_eq_mul]
  push_cast
  rw [realJet_complexify, he]

theorem weight_coordinate (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t)
    (n : ℕ) (P : Polynomial ℝ) :
    (∫ᵛ x : ℝ, ((P.eval x:ℝ):ℂ)*
      (weight n (HigherHeatSignedLaws.realKernel m hm t ht) x:ℂ)
      ∂<•HigherHeatSignedLaws.law m hm t ht) =
      ((coordinate (2*m) ((-1:ℝ)^(m+1)*(t:ℝ)) n P:ℝ):ℂ) := by
  rw [HigherHeatSignedLaws.law, polynomial_weight_integral]
  simp_rw [numerator_eq_density]
  exact density_coordinate m hm t ht n P

end OperatorDerivativeRewrite.Foundation.HigherHeatAppellDuals
