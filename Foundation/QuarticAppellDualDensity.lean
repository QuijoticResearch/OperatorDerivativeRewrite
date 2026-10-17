import Foundation.QuarticAppellPairing

/-! Coordinate duals as actual Schwartz densities, and failure of a polynomial global dual. -/
noncomputable section
open Polynomial MeasureTheory
open scoped SchwartzMap NNReal
namespace OperatorDerivativeRewrite.Foundation.QuarticAppellDualDensity
open QuarticAppellCalculus QuarticAppellExpansion QuarticAppellPairing
open PseudoClarkOconeObstruction HigherHeatSpatialGenerator

theorem no_polynomial_dual_one (a : ℝ) (ha : a ≠ 0) :
    ¬ ∃ Q : Polynomial ℝ, ∀ n : ℕ,
      pairing 4 a (appell a n) Q = if n=1 then 1 else 0 := by
  rintro ⟨Q, hQ⟩
  have hn : Q ≠ 0 := by
    intro hz
    have h := hQ 1
    simp [hz, pairing] at h
  have h := polynomial_top_ne_zero a ha Q hn
  apply h
  rw [hQ, if_neg (by omega : 3*Q.natDegree ≠ 1)]

theorem coordinate_one_not_polynomial_pairing (a : ℝ) (ha : a ≠ 0) :
    ¬ ∃ Q : Polynomial ℝ, ∀ P : Polynomial ℝ,
      pairing 4 a P Q = coordinate a 1 P := by
  rintro ⟨Q, hQ⟩
  apply no_polynomial_dual_one a ha
  refine ⟨Q, fun n => ?_⟩
  rw [hQ, coordinate_appell]

def density (t : ℝ≥0) (ht : 0 < t) (n : ℕ) : 𝓢(ℝ,ℂ) :=
  ((-1:ℂ)^n / (n.factorial:ℂ)) •
    jet n (GaussianSchwartzKernel.evenKernel 2 (by norm_num) t ht)

theorem density_polynomial_integrable (t : ℝ≥0) (ht : 0 < t) (n : ℕ)
    (P : Polynomial ℝ) : Integrable (fun x : ℝ => ((P.eval x:ℝ):ℂ)*density t ht n x) :=
  SchwartzPolynomialPairing.weighted_integrable P (density t ht n)

theorem density_coordinate (t : ℝ≥0) (ht : 0 < t) (n : ℕ) (P : Polynomial ℝ) :
    (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*density t ht n x) =
      (((basis (-(t:ℝ))).repr P n : ℝ):ℂ) := by
  have hs : (-1:ℂ)^n * (-1:ℂ)^n = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    _ = ((-1:ℂ)^n / (n.factorial:ℂ)) *
        (∫ x : ℝ, ((P.eval x:ℝ):ℂ)*
          jet n (GaussianSchwartzKernel.evenKernel 2 (by norm_num) t ht) x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp [density]; ring
    _ = _ := by
      rw [SchwartzPolynomialPairing.polynomial_jet_ibp,
        HigherHeatPolynomialRealization.complex_expectation, actual_coordinate t ht P n]
      push_cast
      calc
        _ = ((-1:ℂ)^n * (-1:ℂ)^n) *
            ((HigherHeatPolynomialRealization.kernelExpectation 2 (by norm_num) t ht
              (derivative^[n] P):ℂ) / (n.factorial:ℂ)) := by ring
        _ = _ := by rw [hs, one_mul]

theorem density_biorthogonal (t : ℝ≥0) (ht : 0 < t) (n k : ℕ) :
    (∫ x : ℝ, (((appell (-(t:ℝ)) k).eval x:ℝ):ℂ)*density t ht n x) =
      if k=n then 1 else 0 := by
  rw [density_coordinate, ← Module.Basis.coord_apply, ← coordinate_eq_basis_coord,
    coordinate_appell]
  split_ifs <;> norm_num

end OperatorDerivativeRewrite.Foundation.QuarticAppellDualDensity
