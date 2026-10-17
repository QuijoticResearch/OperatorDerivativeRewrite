import Foundation.GaussianShearCentroid

/-! Finite-sector centroid algebra for four distinct occupied ray labels.
The unused sectors and their uniform-baseline excess are included explicitly. -/
noncomputable section
open scoped BigOperators
namespace OperatorDerivativeRewrite.Foundation.FiniteRayCentroid
variable {ι : Type*} [Fintype ι]
set_option backward.isDefEq.respectTransparency false

def spread (L : Fin 4 ↪ ι) (v : Fin 4 → ℝ) (j : ι) : ℝ := by
  classical
  exact ∑ r : Fin 4, if L r = j then v r else 0

theorem spread_image (L : Fin 4 ↪ ι) (v : Fin 4 → ℝ) (r : Fin 4) :
    spread L v (L r) = v r := by
  classical
  simp [spread, L.injective.eq_iff]

theorem spread_outside (L : Fin 4 ↪ ι) (v : Fin 4 → ℝ) (j : ι) (hj : j ∉ Set.range L) :
    spread L v j = 0 := by
  classical
  have hn (r : Fin 4) : L r ≠ j := by intro h; exact hj ⟨r,h⟩
  simp [spread, hn]

theorem sum_spread (L : Fin 4 ↪ ι) (v : Fin 4 → ℝ) :
    (∑ j, spread L v j) = ∑ r, v r := by
  classical
  simp [spread, Finset.sum_comm]

theorem spread_mul (L : Fin 4 ↪ ι) (v w : Fin 4 → ℝ) (j : ι) :
    spread L v j*spread L w j = spread L (fun r => v r*w r) j := by
  by_cases h : j ∈ Set.range L
  · obtain ⟨r,rfl⟩ := h
    rw [spread_image, spread_image, spread_image]
  · rw [spread_outside L v j h, spread_outside L w j h,
      spread_outside L (fun r => v r*w r) j h]
    simp

def rays (a b : ℝ) : Fin 4 → ℝ := ![a,a,b,b]
def energy (L : Fin 4 ↪ ι) (a b : ℝ) : ι → ℝ := spread L (rays a b)

theorem sum_energy (L : Fin 4 ↪ ι) (a b : ℝ) : (∑ j, energy L a b j) = 2*(a+b) := by
  rw [energy, sum_spread]
  simp [rays, Fin.sum_univ_succ]
  ring

theorem square_energy (L : Fin 4 ↪ ι) (a b : ℝ) :
    (∑ j, (energy L a b j)^2) = 2*(a^2+b^2) := by
  simp only [pow_two, energy, spread_mul]
  rw [sum_spread]
  simp [rays, Fin.sum_univ_succ]
  ring

theorem cross_energy (L : Fin 4 ↪ ι) (a b d : ℝ) :
    (∑ j, energy L a b j*energy L d b j) = 2*(a*d+b^2) := by
  simp only [energy, spread_mul]
  rw [sum_spread]
  simp [rays, Fin.sum_univ_succ]
  ring

def excess (L : Fin 4 ↪ ι) (a b : ℝ) (j : ι) : ℝ :=
  energy L a b j/(2*(a+b))-1/(Fintype.card ι : ℝ)
def variance (L : Fin 4 ↪ ι) (a b : ℝ) : ℝ := ∑ j, (excess L a b j)^2
def numerator (L : Fin 4 ↪ ι) (a b d : ℝ) : ℝ :=
  ∑ j, excess L a b j*energy L d b j/(2*(a+b))
def ratio (L : Fin 4 ↪ ι) (a b d : ℝ) : ℝ :=
  numerator L a b d/(((d+b)/(a+b))*variance L a b)

theorem card_four (L : Fin 4 ↪ ι) : 4 ≤ Fintype.card ι := by
  simpa using Fintype.card_le_of_injective L L.injective

theorem variance_exact (L : Fin 4 ↪ ι) (a b : ℝ) (hT : a+b ≠ 0) :
    variance L a b = (a^2+b^2)/(2*(a+b)^2)-1/(Fintype.card ι : ℝ) := by
  have hJ : (Fintype.card ι : ℝ) ≠ 0 := by
    have h := card_four L
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have he (j : ι) : (excess L a b j)^2 =
      (energy L a b j)^2/(4*(a+b)^2)-
        energy L a b j/((Fintype.card ι : ℝ)*(a+b))+
        1/(Fintype.card ι : ℝ)^2 := by unfold excess; field_simp; ring
  unfold variance
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.sum_div, square_energy, sum_energy]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  <;> ring

theorem numerator_exact (L : Fin 4 ↪ ι) (a b d : ℝ) (hT : a+b ≠ 0) :
    numerator L a b d = (a*d+b^2)/(2*(a+b)^2)-
      (d+b)/((Fintype.card ι : ℝ)*(a+b)) := by
  have hJ : (Fintype.card ι : ℝ) ≠ 0 := by
    have h := card_four L
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  have he (j : ι) : excess L a b j*energy L d b j/(2*(a+b)) =
      (energy L a b j*energy L d b j)/(4*(a+b)^2)-
        energy L d b j/(2*(Fintype.card ι : ℝ)*(a+b)) := by unfold excess; field_simp; ring
  unfold numerator
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    cross_energy, sum_energy]
  field_simp
  <;> ring

theorem defect_exact (L : Fin 4 ↪ ι) (a b d : ℝ) (hT : a+b ≠ 0) :
    numerator L a b d-((d+b)/(a+b))*variance L a b =
      b*(a-b)*(d-a)/(2*(a+b)^3) := by
  have hJ : (Fintype.card ι : ℝ) ≠ 0 := by
    have h := card_four L
    exact_mod_cast (by omega : Fintype.card ι ≠ 0)
  rw [numerator_exact L a b d hT, variance_exact L a b hT]
  field_simp
  <;> ring

theorem variance_positive (L : Fin 4 ↪ ι) (a b : ℝ) (hb : 0 < b) (hba : b < a) :
    0 < variance L a b := by
  have ha : 0 < a := hb.trans hba
  have hJ : (4 : ℝ) ≤ Fintype.card ι := by exact_mod_cast card_four L
  have hJp : 0 < (Fintype.card ι : ℝ) := by linarith
  have hTp : 0 < 2*(a+b) := by positivity
  have he : 0 < excess L a b (L 0) := by
    rw [excess, energy, spread_image]
    change 0 < a/(2*(a+b))-1/(Fintype.card ι : ℝ)
    rw [sub_pos, div_lt_div_iff₀ hJp hTp]
    have hm := mul_le_mul_of_nonneg_left hJ ha.le
    nlinarith
  unfold variance
  exact lt_of_lt_of_le (sq_pos_of_pos he)
    (Finset.single_le_sum (fun j _ => sq_nonneg (excess L a b j)) (Finset.mem_univ (L 0)))

theorem ratio_gt_one (L : Fin 4 ↪ ι) (a b d : ℝ)
    (hb : 0 < b) (hba : b < a) (had : a < d) : 1 < ratio L a b d := by
  have ha : 0 < a := hb.trans hba
  have hd : 0 < d := ha.trans had
  have hTp : 0 < a+b := add_pos ha hb
  have hden : 0 < ((d+b)/(a+b))*variance L a b :=
    mul_pos (div_pos (add_pos hd hb) hTp) (variance_positive L a b hb hba)
  have hdef : 0 < numerator L a b d-((d+b)/(a+b))*variance L a b := by
    rw [defect_exact L a b d (ne_of_gt hTp)]
    positivity
  rw [ratio, lt_div_iff₀ hden]
  linarith

end OperatorDerivativeRewrite.Foundation.FiniteRayCentroid
