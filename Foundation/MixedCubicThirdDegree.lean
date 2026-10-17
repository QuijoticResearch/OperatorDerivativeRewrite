import Foundation.MixedCubicMomentPositivity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Exact degree-three square positivity for the actual mixed moment functional. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.MixedCubicThirdDegree
open Polynomial MixedCubicMomentPositivity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem moments_five_six (v k : ℝ) :
    moment v k 5 = 10*v*k ∧ moment v k 6 = 15*v^3+10*k^2 := by
  norm_num [moment]
  constructor <;> ring

def cubic (c b a d : ℝ) : Polynomial ℝ :=
  c • X^0 + b • X^1 + a • X^2 + d • X^3

theorem cubic_natDegree (c b a d : ℝ) : (cubic c b a d).natDegree ≤ 3 := by
  have he : cubic c b a d = C d*X^3+C a*X^2+C b*X+C c := by
    simp only [cubic, smul_eq_C_mul, pow_zero, pow_one, mul_one]
    ring
  rw [he]
  exact natDegree_cubic_le

theorem cubic_of_natDegree (g : Polynomial ℝ) (hg : g.natDegree ≤ 3) :
    g = cubic (g.coeff 0) (g.coeff 1) (g.coeff 2) (g.coeff 3) := by
  ext n
  rcases n with _ | (_ | (_ | (_ | n)))
  · norm_num only [cubic, coeff_add, coeff_smul, coeff_X_pow, smul_eq_mul]
    simp only [ite_true, ite_false, mul_one, mul_zero, add_zero]
  · norm_num only [cubic, coeff_add, coeff_smul, coeff_X_pow, smul_eq_mul]
    simp only [ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero]
  · norm_num only [cubic, coeff_add, coeff_smul, coeff_X_pow, smul_eq_mul]
    simp only [ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero]
  · norm_num only [cubic, coeff_add, coeff_smul, coeff_X_pow, smul_eq_mul]
    simp only [ite_true, ite_false, mul_one, mul_zero, zero_add, add_zero]
  · have hz := natDegree_le_iff_coeff_eq_zero.mp hg (n+4) (by omega)
    change g.coeff (n+4) = _
    rw [hz]
    simp only [cubic, coeff_add, coeff_smul, coeff_X_pow,
      ite_eq_right (show n+4 ≠ 0 by omega), ite_eq_right (show n+4 ≠ 1 by omega),
      ite_eq_right (show n+4 ≠ 2 by omega), ite_eq_right (show n+4 ≠ 3 by omega),
      smul_zero, zero_add]

theorem cubic_square (v k c b a d : ℝ) :
    expectation v k ((cubic c b a d)^2) =
      c^2+v*(b^2+2*c*a)+k*(2*c*d+2*b*a)+3*v^2*(a^2+2*b*d)+
        20*v*k*a*d+(15*v^3+10*k^2)*d^2 := by
  have he : (cubic c b a d)^2 = c^2 • (X : Polynomial ℝ)^0 +
      (2*c*b) • X^1 + (b^2+2*c*a) • X^2 + (2*c*d+2*b*a) • X^3 +
      (a^2+2*b*d) • X^4 + (2*a*d) • X^5 + d^2 • X^6 := by
    simp only [cubic, Algebra.smul_def, map_add, map_mul, map_pow,
      map_ofNat, pow_zero, pow_one]
    ring
  rw [he]
  simp only [map_add, map_smul, expectation_X_pow, smul_eq_mul]
  rcases low_moments v k with ⟨h0,h1,h2,h3,h4⟩
  rcases moments_five_six v k with ⟨h5,h6⟩
  rw [h0,h1,h2,h3,h4,h5,h6]
  ring

/-- Coordinates in the basis 1, X, X²-v, X³-k-3vX. -/
def centered (v k c b a d : ℝ) : Polynomial ℝ :=
  cubic (c-v*a-k*d) (b-3*v*d) a d

theorem centered_natDegree (v k c b a d : ℝ) : (centered v k c b a d).natDegree ≤ 3 :=
  cubic_natDegree _ _ _ _

theorem cubic_as_centered (v k c b a d : ℝ) :
    cubic c b a d = centered v k (c+v*a+k*d) (b+3*v*d) a d := by
  simp only [centered, cubic, Algebra.smul_def, map_sub, map_add, map_mul, map_ofNat]
  ring

theorem centered_square (v k c b a d : ℝ) :
    expectation v k ((centered v k c b a d)^2) =
      c^2+v*b^2+2*k*a*b+2*v^2*a^2+12*v*k*a*d+(6*v^3+9*k^2)*d^2 := by
  rw [centered, cubic_square]
  ring

def delta (v k : ℝ) : ℝ := 2*v^3-k^2
def determinant (v k : ℝ) : ℝ := 12*v^6-24*v^3*k^2-9*k^4

def centeredGram (v k : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![v, k, 0; k, 2*v^2, 6*v*k; 0, 6*v*k, 6*v^3+9*k^2]

theorem centered_gram_identity (v k b a d : ℝ) :
    expectation v k ((centered v k 0 b a d)^2) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (![b,a,d] : Fin 3 → ℝ) i * centeredGram v k i j * (![b,a,d] : Fin 3 → ℝ) j := by
  rw [centered_square]
  simp [centeredGram, Fin.sum_univ_succ]; ring

theorem centeredGram_det (v k : ℝ) : (centeredGram v k).det = determinant v k := by
  simp [Matrix.det_fin_three, centeredGram, determinant]; ring

theorem weighted_square_decomposition (v k c b a d : ℝ) :
    v*delta v k*expectation v k ((centered v k c b a d)^2) =
      v*delta v k*c^2+delta v k*(v*b+k*a)^2+
        (delta v k*a+6*v^2*k*d)^2+v*determinant v k*d^2 := by
  rw [centered_square]
  unfold delta determinant
  ring

theorem determinant_witness_value (v k : ℝ) :
    expectation v k ((centered v k 0 (6*v*k^2) (-6*v^2*k) (delta v k))^2) =
      delta v k*determinant v k := by
  rw [centered_square]
  unfold delta determinant
  ring

theorem boundary_witness_value (v k : ℝ) (hd : delta v k = 0) :
    expectation v k ((centered v k 0 (-4*v*k) (4*v^2) (-k))^2) = -48*v^6 := by
  have hk : k^2 = 2*v^3 := by unfold delta at hd; linarith
  rw [centered_square]
  calc
    _ = 32*v^6-58*v^3*k^2+9*(k^2)^2 := by ring
    _ = _ := by rw [hk]; ring

theorem determinant_nonneg_delta_pos (v k : ℝ) (hv : 0 < v)
    (hD : 0 ≤ determinant v k) : 0 < delta v k := by
  by_contra hnot
  have hk : 2*v^3 ≤ k^2 := by unfold delta at hnot; linarith
  have hm := mul_nonneg (pow_nonneg hv.le 3) (sub_nonneg.mpr hk)
  unfold determinant at hD
  nlinarith [sq_nonneg (k^2), pow_pos hv 6]

theorem centered_square_nonneg (v k : ℝ) (hv : 0 < v) (hD : 0 ≤ determinant v k)
    (c b a d : ℝ) : 0 ≤ expectation v k ((centered v k c b a d)^2) := by
  have hd := determinant_nonneg_delta_pos v k hv hD
  have hn := add_nonneg (add_nonneg
    (add_nonneg (mul_nonneg (mul_pos hv hd).le (sq_nonneg c))
      (mul_nonneg hd.le (sq_nonneg (v*b+k*a))))
    (sq_nonneg (delta v k*a+6*v^2*k*d)))
    (mul_nonneg (mul_nonneg hv.le hD) (sq_nonneg d))
  rw [← weighted_square_decomposition] at hn
  exact (mul_nonneg_iff_of_pos_left (mul_pos hv hd)).mp hn

theorem cubic_positivity_iff (v k : ℝ) (hv : 0 < v) :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 3 → 0 ≤ expectation v k (g^2)) ↔
      0 ≤ determinant v k := by
  constructor
  · intro hpos
    have hq : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 → 0 ≤ expectation v k (g^2) :=
      fun g hg => hpos g (hg.trans (by omega))
    have hd0 : 0 ≤ delta v k := sub_nonneg.mpr ((quadratic_positivity_iff v k).mp hq).2
    have hd : 0 < delta v k := by
      by_contra hnot
      have hz : delta v k = 0 := le_antisymm (le_of_not_gt hnot) hd0
      have hw := hpos (centered v k 0 (-4*v*k) (4*v^2) (-k)) (centered_natDegree _ _ _ _ _ _)
      rw [boundary_witness_value v k hz] at hw
      nlinarith [pow_pos hv 6]
    have hw := hpos (centered v k 0 (6*v*k^2) (-6*v^2*k) (delta v k))
      (centered_natDegree _ _ _ _ _ _)
    rw [determinant_witness_value] at hw
    exact (mul_nonneg_iff_of_pos_left hd).mp hw
  · intro hD g hg
    rw [cubic_of_natDegree g hg, cubic_as_centered v k]
    exact centered_square_nonneg v k hv hD _ _ _ _

theorem cubic_positivity_all_parameters_iff (v k : ℝ) :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 3 → 0 ≤ expectation v k (g^2)) ↔
      0 ≤ v ∧ 0 ≤ determinant v k := by
  constructor
  · intro hpos
    have hq : ∀ g : Polynomial ℝ, g.natDegree ≤ 2 → 0 ≤ expectation v k (g^2) :=
      fun g hg => hpos g (hg.trans (by omega))
    rcases (quadratic_positivity_iff v k).mp hq with ⟨hv,hk⟩
    refine ⟨hv, ?_⟩
    by_cases hz : v = 0
    · have hk0 : k = 0 := by rw [hz] at hk; nlinarith [sq_nonneg k]
      simp [hz, hk0, determinant]
    · exact (cubic_positivity_iff v k (lt_of_le_of_ne hv (Ne.symm hz))).mp hpos
  · rintro ⟨hv,hD⟩
    by_cases hz : v = 0
    · have hk0 : k = 0 := by
        simp only [determinant, hz] at hD
        have hk2 : k^2 = 0 := by nlinarith [sq_nonneg (k^2)]
        exact sq_eq_zero_iff.mp hk2
      intro g hg
      rw [cubic_of_natDegree g hg, cubic_square, hz, hk0]
      nlinarith [sq_nonneg (g.coeff 0)]
    · exact (cubic_positivity_iff v k (lt_of_le_of_ne hv (Ne.symm hz))).mpr hD

theorem determinant_witness_calibrates : centered 1 1 0 6 (-6) 1 = cubicWitness := by
  norm_num [centered, cubic, cubicWitness, Algebra.smul_def]; ring

end OperatorDerivativeRewrite.Foundation.MixedCubicThirdDegree
