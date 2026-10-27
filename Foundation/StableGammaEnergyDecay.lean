import Foundation.CauchyCenteredEnergy

/-! Actual circle-integrated finite Gamma energies have diagonal Fourier
weights and exact dissipation along the stable coefficient semigroup.
For distinct nonzero integer frequencies, the sharp exp(-2t) bound holds
at EVERY energy level. No completed-domain or probabilistic realization
for arbitrary positive orders is asserted. -/
noncomputable section
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.StableGammaEnergyDecay
open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace FiniteFourierSynthesis FiniteFourierTorusAverage
open FiniteStableGamma.Core BrownianEnergyRepair.Torus CauchyCenteredEnergy

theorem circle_gamma_diagonal {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (n : Fin N → ℤ) (hn : Function.Injective n) (c : Fin N → ℂ) (q : ℕ) (x : Space) :
    circleAverage 0 (fun y => synthesis y
      (gammaIter (stableSymbol γ) q (axisPolynomial n c) (axisPolynomial n c))) x =
      ∑ i, ((|(n i : ℝ)|^γ : ℝ) : ℂ)^q * conj (c i) * c i := by
  rw [circleAverage_synthesis]
  unfold axisPolynomial
  rw [gammaIter_finite]
  simp [map_sum, cut_single, synthesis_single, axisWave, hn.eq_iff,
    sub_eq_zero, character_zero, kernel, stableSymbol, Real.zero_rpow (ne_of_gt hγ)]

def energy {N : ℕ} (γ : ℝ) (n : Fin N → ℤ) (q : ℕ) (c : Fin N → ℂ) : ℝ :=
  (circleAverage 0 (fun y => synthesis y
    (gammaIter (stableSymbol γ) q (axisPolynomial n c) (axisPolynomial n c))) 0).re

theorem energy_diagonal {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (n : Fin N → ℤ) (hn : Function.Injective n) (q : ℕ) (c : Fin N → ℂ) :
    energy γ n q c = ∑ i, (|(n i : ℝ)|^γ)^q * ‖c i‖^2 := by
  rw [energy, circle_gamma_diagonal γ hγ n hn]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_assoc, mul_comm (conj (c i)) (c i), Complex.mul_conj']
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

def coefficientsAt {N : ℕ} (γ : ℝ) (n : Fin N → ℤ) (t : ℝ) (c : Fin N → ℂ) : Fin N → ℂ :=
  fun i => (Real.exp (-|(n i : ℝ)|^γ*t) : ℂ) * c i

theorem energy_at {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (n : Fin N → ℤ) (hn : Function.Injective n) (q : ℕ) (t : ℝ) (c : Fin N → ℂ) :
    energy γ n q (coefficientsAt γ n t c) =
      ∑ i, (|(n i : ℝ)|^γ)^q * Real.exp (-2*|(n i : ℝ)|^γ*t) * ‖c i‖^2 := by
  rw [energy_diagonal γ hγ n hn]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coefficientsAt, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  rw [show -|(n i : ℝ)|^γ*t + -|(n i : ℝ)|^γ*t = -2*|(n i : ℝ)|^γ*t by ring]
  ring

theorem coefficientsAt_add {N : ℕ} (γ : ℝ) (n : Fin N → ℤ)
    (s t : ℝ) (c : Fin N → ℂ) :
    coefficientsAt γ n (s+t) c = coefficientsAt γ n s (coefficientsAt γ n t c) := by
  funext i
  simp only [coefficientsAt, mul_add, Real.exp_add, Complex.ofReal_mul]
  ring

theorem coefficientsAt_zero {N : ℕ} (γ : ℝ) (n : Fin N → ℤ) (c : Fin N → ℂ) :
    coefficientsAt γ n 0 c = c := by
  funext i
  simp [coefficientsAt]

theorem nonzero_frequency_gap (γ : ℝ) (hγ : 0 ≤ γ) (m : ℤ) (hm : m ≠ 0) :
    1 ≤ |(m : ℝ)|^γ := by
  apply Real.one_le_rpow _ hγ
  have hi : (1 : ℤ) ≤ |m| := by
    rcases lt_or_gt_of_ne hm with h | h
    · rw [abs_of_neg h]; omega
    · rw [abs_of_pos h]; omega
  exact_mod_cast hi

theorem energy_decay_all_orders {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (n : Fin N → ℤ) (hn : Function.Injective n) (hz : ∀ i, n i ≠ 0)
    (q : ℕ) (t : ℝ) (ht : 0 ≤ t) (c : Fin N → ℂ) :
    energy γ n q (coefficientsAt γ n t c) ≤ Real.exp (-2*t) * energy γ n q c := by
  rw [energy_at γ hγ n hn, energy_diagonal γ hγ n hn, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hw := nonzero_frequency_gap γ hγ.le (n i) (hz i)
  have he : Real.exp (-2*|(n i : ℝ)|^γ*t) ≤ Real.exp (-2*t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hp : 0 ≤ (|(n i : ℝ)|^γ)^q := pow_nonneg (Real.rpow_nonneg (abs_nonneg _) _) _
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hp) (sq_nonneg ‖c i‖)
  nlinarith

theorem energy_dissipation {N : ℕ} (γ : ℝ) (hγ : 0 < γ)
    (n : Fin N → ℤ) (hn : Function.Injective n) (q : ℕ) (c : Fin N → ℂ) (t : ℝ) :
    HasDerivAt (fun s => energy γ n q (coefficientsAt γ n s c))
      (-2 * energy γ n (q+1) (coefficientsAt γ n t c)) t := by
  have he : (fun s => energy γ n q (coefficientsAt γ n s c)) =
      (fun s => ∑ i, (|(n i : ℝ)|^γ)^q * Real.exp (-2*|(n i : ℝ)|^γ*s) * ‖c i‖^2) :=
    funext (fun s => energy_at γ hγ n hn q s c)
  rw [he, energy_at γ hγ n hn]
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (((Real.hasDerivAt_exp _).comp t ((hasDerivAt_id t).const_mul (-2*|(n i : ℝ)|^γ))).const_mul
      ((|(n i : ℝ)|^γ)^q)).mul_const (‖c i‖^2))
  convert hd using 1
  · funext s
    simp
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [pow_succ, id_eq]
    ring

theorem first_frequency_exact (γ : ℝ) (hγ : 0 < γ) (q : ℕ) (t : ℝ) :
    energy γ (fun _ : Fin 1 => (1 : ℤ)) q
      (coefficientsAt γ (fun _ => 1) t (fun _ => 1)) = Real.exp (-2*t) := by
  rw [energy_at γ hγ _ (fun i j _ => Subsingleton.elim i j)]
  simp

theorem generator_axis {N : ℕ} (γ : ℝ) (n : Fin N → ℤ) (c : Fin N → ℂ) :
    generator (stableSymbol γ) (axisPolynomial n c) =
      axisPolynomial n (fun i => -((|(n i : ℝ)|^γ : ℝ) : ℂ)*c i) := by
  simp [axisPolynomial, generator_single, stableSymbol, axisWave]

end OperatorDerivativeRewrite.Foundation.StableGammaEnergyDecay
