import Foundation.MixedCubicInteriorQuartic

/-! Exact degree-four square positivity for the actual mixed polynomial functional. -/
noncomputable section
open Polynomial Matrix
namespace OperatorDerivativeRewrite.Foundation.MixedCubicFourthDegree
open MixedCubicMomentPositivity MixedCubicThirdDegree
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def quartic (c b a d e : ℝ) : Polynomial ℝ := cubic c b a d+e • X^4

theorem quartic_degree (c b a d e : ℝ) : (quartic c b a d e).natDegree ≤ 4 := by
  have hc : (cubic c b a d).natDegree ≤ 4 := (cubic_natDegree c b a d).trans (by omega)
  have he : (e • (X^4 : Polynomial ℝ)).natDegree ≤ 4 :=
    (natDegree_smul_le e (X^4 : Polynomial ℝ)).trans (by simp)
  simpa only [quartic,Nat.max_self] using natDegree_add_le_of_le hc he

theorem quartic_of_natDegree (g : Polynomial ℝ) (hg : g.natDegree ≤ 4) :
    g = quartic (g.coeff 0) (g.coeff 1) (g.coeff 2) (g.coeff 3) (g.coeff 4) := by
  calc
    g = ∑ n ∈ Finset.range 5, C (g.coeff n)*X^n :=
      g.as_sum_range_C_mul_X_pow' (by omega)
    _ = _ := by
      simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add]
      simp only [quartic,cubic,smul_eq_C_mul]

theorem quartic_square (v k c b a d e : ℝ) :
    expectation v k ((quartic c b a d e)^2) =
      c^2+v*(b^2+2*c*a)+k*(2*c*d+2*b*a)+3*v^2*(a^2+2*c*e+2*b*d)+
      20*v*k*(b*e+a*d)+(15*v^3+10*k^2)*(d^2+2*a*e)+
      210*v^2*k*d*e+(105*v^4+280*v*k^2)*e^2 := by
  have he : (quartic c b a d e)^2 = c^2 • (X : Polynomial ℝ)^0+
      (2*c*b) • X^1+(b^2+2*c*a) • X^2+(2*c*d+2*b*a) • X^3+
      (a^2+2*c*e+2*b*d) • X^4+(2*b*e+2*a*d) • X^5+
      (d^2+2*a*e) • X^6+(2*d*e) • X^7+e^2 • X^8 := by
    simp only [quartic,cubic,Algebra.smul_def,map_add,map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [map_add,map_smul,smul_eq_mul,expectation_X_pow]
  norm_num [moment]
  ring

def fourthHermite (v k : ℝ) : Polynomial ℝ :=
  X^4-(6*v) • X^2-(4*k) • X^1+(3*v^2) • X^0

def centeredQuartic (v k c b a d e : ℝ) : Polynomial ℝ :=
  centered v k c b a d+e • fourthHermite v k

theorem centeredQuartic_expansion (v k c b a d e : ℝ) :
    centeredQuartic v k c b a d e =
      quartic (c-v*a-k*d+3*v^2*e) (b-3*v*d-4*k*e) (a-6*v*e) d e := by
  simp only [centeredQuartic,fourthHermite,centered,quartic,cubic,Algebra.smul_def,
    map_add,map_sub,map_mul,map_pow,map_ofNat,map_neg]
  ring

theorem centeredQuartic_degree (v k c b a d e : ℝ) :
    (centeredQuartic v k c b a d e).natDegree ≤ 4 := by
  rw [centeredQuartic_expansion]
  exact quartic_degree _ _ _ _ _

theorem quartic_as_centered (v k c b a d e : ℝ) :
    quartic c b a d e = centeredQuartic v k
      (c+v*a+k*d+3*v^2*e) (b+3*v*d+4*k*e) (a+6*v*e) d e := by
  rw [centeredQuartic_expansion]
  congr 1 <;> ring

theorem centeredQuartic_square (v k c b a d e : ℝ) :
    expectation v k ((centeredQuartic v k c b a d e)^2) =
      c^2+v*b^2+2*k*a*b+2*v^2*a^2+12*v*k*a*d+(6*v^3+9*k^2)*d^2+
      12*k^2*a*e+72*v^2*k*d*e+(24*v^4+144*v*k^2)*e^2 := by
  rw [centeredQuartic_expansion,quartic_square]
  ring

def fourthDeterminant (v k : ℝ) : ℝ := 288*v^10-1440*v^7*k^2-1620*v*k^6

def centeredGram4 (v k : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![v,k,0,0; k,2*v^2,6*v*k,6*k^2;
     0,6*v*k,6*v^3+9*k^2,36*v^2*k;
     0,6*k^2,36*v^2*k,24*v^4+144*v*k^2]

theorem centeredGram4_identity (v k b a d e : ℝ) :
    expectation v k ((centeredQuartic v k 0 b a d e)^2) =
      ∑ i : Fin 4, ∑ j : Fin 4,
        (![b,a,d,e] : Fin 4 → ℝ) i*centeredGram4 v k i j*(![b,a,d,e] : Fin 4 → ℝ) j := by
  rw [centeredQuartic_square]
  simp [centeredGram4,Fin.sum_univ_succ]
  ring

theorem centeredGram4_det (v k : ℝ) : (centeredGram4 v k).det = fourthDeterminant v k := by
  rw [Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ,centeredGram4,Matrix.submatrix,Matrix.det_fin_three,
    fourthDeterminant,Fin.succAbove]
  ring

theorem weighted_quartic_decomposition (v k c b a d e : ℝ) :
    v*delta v k*determinant v k*expectation v k ((centeredQuartic v k c b a d e)^2) =
      v*delta v k*determinant v k*c^2+
      delta v k*determinant v k*(v*b+k*a)^2+
      determinant v k*(delta v k*a+6*v^2*k*d+6*v*k^2*e)^2+
      v*(determinant v k*d+72*v^2*k*(v^3-k^2)*e)^2+
      v*delta v k*fourthDeterminant v k*e^2 := by
  rw [centeredQuartic_square]
  unfold delta determinant fourthDeterminant
  ring

def determinantQuartic (v k : ℝ) : Polynomial ℝ :=
  centeredQuartic v k 0 (-18*k^3*(10*v^3-3*k^2))
    (18*v*k^2*(10*v^3-3*k^2)) (-72*v^2*k*(v^3-k^2)) (determinant v k)

theorem determinantQuartic_degree (v k : ℝ) : (determinantQuartic v k).natDegree ≤ 4 :=
  centeredQuartic_degree _ _ _ _ _ _ _

theorem determinantQuartic_value (v k : ℝ) :
    expectation v k ((determinantQuartic v k)^2) = determinant v k*fourthDeterminant v k := by
  rw [determinantQuartic,centeredQuartic_square]
  unfold determinant fourthDeterminant
  ring

theorem fourth_nonneg_cubic_pos (v k : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k) :
    0 < determinant v k := by
  have hin : 0 ≤ 8*v^9-40*v^6*k^2-45*k^6 := by
    apply (mul_nonneg_iff_of_pos_left (mul_pos (by norm_num : (0 : ℝ) < 36) hv)).mp
    convert h4 using 1 <;> unfold fourthDeterminant <;> ring
  have hfac : 0 ≤ v^6*(8*v^3-40*k^2) := by nlinarith [sq_nonneg (k^3)]
  have hb : 5*k^2 ≤ v^3 := by
    have hx := (mul_nonneg_iff_of_pos_left (pow_pos hv 6)).mp hfac
    linarith
  have h1 := mul_nonneg (pow_nonneg hv.le 3) (sub_nonneg.mpr hb)
  have h2 := mul_nonneg (sq_nonneg k) (sub_nonneg.mpr hb)
  unfold determinant
  nlinarith [pow_pos hv 6]

theorem centeredQuartic_nonneg (v k : ℝ) (hv : 0 < v) (h4 : 0 ≤ fourthDeterminant v k)
    (c b a d e : ℝ) : 0 ≤ expectation v k ((centeredQuartic v k c b a d e)^2) := by
  have hD := fourth_nonneg_cubic_pos v k hv h4
  have hd := determinant_nonneg_delta_pos v k hv hD.le
  have hn := add_nonneg (add_nonneg (add_nonneg (add_nonneg
    (mul_nonneg (mul_pos (mul_pos hv hd) hD).le (sq_nonneg c))
    (mul_nonneg (mul_pos hd hD).le (sq_nonneg (v*b+k*a))))
    (mul_nonneg hD.le (sq_nonneg (delta v k*a+6*v^2*k*d+6*v*k^2*e))))
    (mul_nonneg hv.le (sq_nonneg (determinant v k*d+72*v^2*k*(v^3-k^2)*e))))
    (mul_nonneg (mul_nonneg (mul_pos hv hd).le h4) (sq_nonneg e))
  rw [← weighted_quartic_decomposition] at hn
  exact (mul_nonneg_iff_of_pos_left (mul_pos (mul_pos hv hd) hD)).mp hn

theorem quartic_positivity_iff (v k : ℝ) (hv : 0 < v) :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 4 → 0 ≤ expectation v k (g^2)) ↔
      0 ≤ fourthDeterminant v k := by
  constructor
  · intro hp
    have hD0 := (cubic_positivity_iff v k hv).mp (fun g hg => hp g (hg.trans (by omega)))
    have hD : 0 < determinant v k := by
      by_contra hn
      have hz := le_antisymm (le_of_not_gt hn) hD0
      exact MixedCubicBoundaryQuartic.boundary_not_quartic_positive v k hv hz hp
    have hw := hp (determinantQuartic v k) (determinantQuartic_degree v k)
    rw [determinantQuartic_value] at hw
    exact (mul_nonneg_iff_of_pos_left hD).mp hw
  · intro h4 g hg
    rw [quartic_of_natDegree g hg,quartic_as_centered v k]
    exact centeredQuartic_nonneg v k hv h4 _ _ _ _ _

theorem quartic_positivity_all_parameters_iff (v k : ℝ) :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 4 → 0 ≤ expectation v k (g^2)) ↔
      (v=0 ∧ k=0) ∨ (0<v ∧ 0≤fourthDeterminant v k) := by
  constructor
  · intro hp
    have hq := (quadratic_positivity_iff v k).mp (fun g hg => hp g (hg.trans (by omega)))
    by_cases hz : v=0
    · have hk : k=0 := by rw [hz] at hq; nlinarith [sq_nonneg k]
      exact Or.inl ⟨hz,hk⟩
    · have hv := lt_of_le_of_ne hq.1 (Ne.symm hz)
      exact Or.inr ⟨hv,(quartic_positivity_iff v k hv).mp hp⟩
  · rintro (⟨rfl,rfl⟩ | ⟨hv,h4⟩)
    · intro g hg
      rw [quartic_of_natDegree g hg,quartic_square]
      norm_num
      positivity
    · exact (quartic_positivity_iff v k hv).mpr h4

theorem fourthDeterminant_normalized (v k : ℝ) (hv : v ≠ 0) :
    fourthDeterminant v k =
      36*v^10*(8-40*(k^2/v^3)-45*(k^2/v^3)^3) := by
  unfold fourthDeterminant
  field_simp [hv]
  ring

theorem normalized_quartic_positivity_iff (v k : ℝ) (hv : 0 < v) :
    (∀ g : Polynomial ℝ, g.natDegree ≤ 4 → 0 ≤ expectation v k (g^2)) ↔
      0 ≤ 8-40*(k^2/v^3)-45*(k^2/v^3)^3 := by
  rw [quartic_positivity_iff v k hv,fourthDeterminant_normalized v k hv.ne']
  exact mul_nonneg_iff_of_pos_left (mul_pos (by norm_num) (pow_pos hv 10))

end OperatorDerivativeRewrite.Foundation.MixedCubicFourthDegree
