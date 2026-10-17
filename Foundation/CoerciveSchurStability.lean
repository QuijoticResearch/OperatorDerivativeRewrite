import Foundation.SchurGaussianInnovation
import Foundation.ManuscriptSchurDiagnostics

/-! Correct variational Schur bounds, with explicit mixed-coupling losses. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.CoerciveSchurStability
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def blockEnergy (a : ℝ) (b : E) (q : E → ℝ) (x : ℝ) (y : E) : ℝ :=
  a*x^2+2*x*inner ℝ b y+q y

theorem scalar_young_lower (c r s : ℝ) (hc : 0 < c) :
    -(r^2/c) ≤ c*s^2-2*r*s := by
  rw [← neg_div]
  apply (div_le_iff₀ hc).mpr
  nlinarith [sq_nonneg (c*s-r)]

/-- Coercivity controls the eliminated energy without an inverse or attainment assumption. -/
theorem coercive_lower (a c ε : ℝ) (b : E) (q : E → ℝ)
    (hc : 0 < c) (hb : ‖b‖ ≤ ε) (hq : ∀ y, c*‖y‖^2 ≤ q y) (x : ℝ) (y : E) :
    (a-ε^2/c)*x^2 ≤ blockEnergy a b q x y := by
  have hi : |inner ℝ b y| ≤ ε*‖y‖ :=
    (abs_real_inner_le_norm b y).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg y))
  have hm : |x*inner ℝ b y| ≤ (|x| *ε)*‖y‖ := by
    rw [abs_mul]
    calc
      _ ≤ |x| *(ε*‖y‖) := mul_le_mul_of_nonneg_left hi (abs_nonneg x)
      _ = _ := by ring
  have hl := neg_le_of_abs_le hm
  have hy := scalar_young_lower c (|x| *ε) ‖y‖ hc
  have he : (|x| *ε)^2/c=(ε^2/c)*x^2 := by rw [mul_pow, sq_abs]; ring
  rw [he] at hy
  unfold blockEnergy
  nlinarith [hq y]

theorem perturbed_boundary_lower (a a0 δ c ε : ℝ) (b : E) (q : E → ℝ)
    (hc : 0 < c) (ha : a0-δ ≤ a) (hb : ‖b‖ ≤ ε)
    (hq : ∀ y, c*‖y‖^2 ≤ q y) (x : ℝ) (y : E) :
    (a0-δ-ε^2/c)*x^2 ≤ blockEnergy a b q x y := by
  have hs := mul_le_mul_of_nonneg_right ha (sq_nonneg x)
  have he := coercive_lower a c ε b q hc hb hq x y
  nlinarith

/-- With half the reference interior coercivity retained, the mixed loss is quadratic. -/
theorem half_coercivity_lower (a a0 δ m ε : ℝ) (b : E) (q : E → ℝ)
    (hm : 0 < m) (ha : a0-δ ≤ a) (hb : ‖b‖ ≤ ε)
    (hq : ∀ y, (m/2)*‖y‖^2 ≤ q y) (x : ℝ) (y : E) :
    (a0-δ-2*ε^2/m)*x^2 ≤ blockEnergy a b q x y := by
  have he := perturbed_boundary_lower a a0 δ (m/2) ε b q (by positivity) ha hb hq x y
  have hd : ε^2/(m/2)=2*ε^2/m := by ring
  simpa only [hd] using he

theorem interior_perturbation_lower (a a0 δ m η ε : ℝ) (b : E) (q q0 : E → ℝ)
    (hm : 0 < m) (hη : η ≤ m/2) (ha : a0-δ ≤ a) (hb : ‖b‖ ≤ ε)
    (hq0 : ∀ y, m*‖y‖^2 ≤ q0 y) (hpert : ∀ y, -η*‖y‖^2 ≤ q y-q0 y)
    (x : ℝ) (y : E) :
    (a0-δ-2*ε^2/m)*x^2 ≤ blockEnergy a b q x y := by
  apply half_coercivity_lower a a0 δ m ε b q hm ha hb
  intro z
  have hs := mul_le_mul_of_nonneg_right hη (sq_nonneg ‖z‖)
  nlinarith [hq0 z, hpert z]

theorem operator_quadratic_perturbation (C C0 : E →L[ℝ] E) (η : ℝ)
    (hC : ‖C-C0‖ ≤ η) (y : E) :
    -η*‖y‖^2 ≤ inner ℝ (C y) y-inner ℝ (C0 y) y := by
  have hy : ‖(C-C0) y‖ ≤ η*‖y‖ :=
    ((C-C0).le_opNorm y).trans (mul_le_mul_of_nonneg_right hC (norm_nonneg y))
  have hi := abs_real_inner_le_norm ((C-C0) y) y
  have hp := mul_le_mul_of_nonneg_right hy (norm_nonneg y)
  have hl := neg_le_of_abs_le hi
  have he : inner ℝ (C y) y-inner ℝ (C0 y) y=inner ℝ ((C-C0) y) y := by
    change inner ℝ (C y) y-inner ℝ (C0 y) y=inner ℝ (C y-C0 y) y
    rw [inner_sub_left]
  rw [he]
  nlinarith

/-- Operator-norm hypotheses yield the zero-reference-coupling estimate directly. -/
theorem operator_robust_lower (a a0 δ m η ε : ℝ) (b : E) (C C0 : E →L[ℝ] E)
    (hm : 0 < m) (hη : η ≤ m/2) (ha : |a-a0| ≤ δ) (hb : ‖b‖ ≤ ε)
    (hC0 : ∀ y, m*‖y‖^2 ≤ inner ℝ (C0 y) y) (hC : ‖C-C0‖ ≤ η)
    (x : ℝ) (y : E) :
    (a0-δ-2*ε^2/m)*x^2 ≤ blockEnergy a b (fun z => inner ℝ (C z) z) x y := by
  apply interior_perturbation_lower a a0 δ m η ε b _ (fun z => inner ℝ (C0 z) z)
    hm hη (by linarith [neg_le_of_abs_le ha]) hb hC0
  exact operator_quadratic_perturbation C C0 η hC

theorem source_slack_lower (a a0 δ m η ε : ℝ) (b : E) (C C0 : E →L[ℝ] E)
    (hm : 0 < m) (hη : η ≤ m/2) (ha : |a-a0| ≤ δ) (hb : ‖b‖ ≤ ε)
    (hC0 : ∀ y, m*‖y‖^2 ≤ inner ℝ (C0 y) y) (hC : ‖C-C0‖ ≤ η)
    (x : ℝ) (y : E) :
    (a0-δ-4*ε^2/m)*x^2 ≤ blockEnergy a b (fun z => inner ℝ (C z) z) x y := by
  have he := operator_robust_lower a a0 δ m η ε b C C0 hm hη ha hb hC0 hC x y
  have hs := mul_nonneg (div_nonneg (sq_nonneg ε) (le_of_lt hm)) (sq_nonneg x)
  have hid : (a0-δ-4*ε^2/m)*x^2=(a0-δ-2*ε^2/m)*x^2-2*((ε^2/m)*x^2) := by ring
  rw [hid]
  linarith

theorem solved_schur_energy (a : ℝ) (b u : E) (C : E →L[ℝ] E) (hu : C u=b) :
    blockEnergy a b (fun z => inner ℝ (C z) z) 1 (-u)=a-inner ℝ b u := by
  simp only [blockEnergy, one_pow, mul_one, map_neg, inner_neg_left, inner_neg_right, hu]
  ring

/-- For a solved interior equation, the actual scalar Schur quantity obeys the same bound. -/
theorem operator_schur_lower (a a0 δ m η ε : ℝ) (b u : E) (C C0 : E →L[ℝ] E)
    (hm : 0 < m) (hη : η ≤ m/2) (ha : |a-a0| ≤ δ) (hb : ‖b‖ ≤ ε)
    (hC0 : ∀ y, m*‖y‖^2 ≤ inner ℝ (C0 y) y) (hC : ‖C-C0‖ ≤ η) (hu : C u=b) :
    a0-δ-2*ε^2/m ≤ a-inner ℝ b u := by
  have he := operator_robust_lower a a0 δ m η ε b C C0 hm hη ha hb hC0 hC 1 (-u)
  rw [solved_schur_energy a b u C hu] at he
  simpa only [one_pow, mul_one] using he

theorem coercive_injective (C : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hC : ∀ y, c*‖y‖^2 ≤ inner ℝ (C y) y) : Function.Injective C := by
  intro u v huv
  have hz : C (u-v)=0 := by rw [map_sub, huv, sub_self]
  have he := hC (u-v)
  rw [hz, inner_zero_left] at he
  have hs : ‖u-v‖^2 ≤ 0 := (mul_le_mul_iff_right₀ hc).mp (by simpa only [mul_zero] using he)
  have hn : ‖u-v‖=0 := by nlinarith [norm_nonneg (u-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

theorem finite_coercive_solution [FiniteDimensional ℝ E] (C : E →L[ℝ] E) (c : ℝ)
    (hc : 0 < c) (hC : ∀ y, c*‖y‖^2 ≤ inner ℝ (C y) y) (b : E) :
    ∃ u, C u=b :=
  LinearMap.surjective_of_injective (f := C.toLinearMap) (coercive_injective C c hc hC) b

theorem scalar_completed_square (a b c x y : ℝ) (hc : c ≠ 0) :
    a*x^2+2*b*x*y+c*y^2=(a-b^2/c)*x^2+c*(y+b/c*x)^2 := by
  field_simp
  ring

theorem scalar_minimum (a b c x : ℝ) (hc : c ≠ 0) :
    a*x^2+2*b*x*(-b/c*x)+c*(-b/c*x)^2=(a-b^2/c)*x^2 := by
  rw [scalar_completed_square a b c x _ hc]
  have he : -b/c*x+b/c*x=0 := by ring
  rw [he]
  simp

theorem half_bound_attained (a ε m x : ℝ) (hm : 0 < m) :
    a*x^2+2*ε*x*(-ε/(m/2)*x)+(m/2)*(-ε/(m/2)*x)^2=(a-2*ε^2/m)*x^2 := by
  have he := scalar_minimum a ε (m/2) x (ne_of_gt (by positivity : 0 < m/2))
  have hd : ε^2/(m/2)=2*ε^2/m := by ring
  simpa only [hd] using he

theorem norm_square_increment (b d : E) : ‖b+d‖^2-‖b‖^2=2*inner ℝ b d+‖d‖^2 := by
  rw [norm_add_sq_real]
  ring

theorem norm_square_increment_bound (b d : E) (ε : ℝ) (hd : ‖d‖ ≤ ε) :
    ‖b+d‖^2-‖b‖^2 ≤ 2*‖b‖*ε+ε^2 := by
  have hε : 0 ≤ ε := (norm_nonneg d).trans hd
  have hi := (real_inner_le_norm b d).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg b))
  have hs : ‖d‖^2 ≤ ε^2 := (sq_le_sq₀ (norm_nonneg d) hε).mpr hd
  rw [norm_square_increment]
  nlinarith

def isotropicSchur (a : ℝ) (b : E) (c : ℝ) : ℝ := a-‖b‖^2/c

/-- A nonzero reference coupling contributes a first-order cross term. -/
theorem isotropic_increment (a c : ℝ) (b d : E) :
    isotropicSchur a (b+d) c=isotropicSchur a b c-(2*inner ℝ b d+‖d‖^2)/c := by
  unfold isotropicSchur
  rw [norm_add_sq_real]
  ring

theorem isotropic_perturbation_lower (a c ε : ℝ) (b d : E) (hc : 0 < c) (hd : ‖d‖ ≤ ε) :
    isotropicSchur a b c-(2*‖b‖*ε+ε^2)/c ≤ isotropicSchur a (b+d) c := by
  have hs := div_le_div_of_nonneg_right (norm_square_increment_bound b d ε hd) (le_of_lt hc)
  unfold isotropicSchur
  rw [sub_div] at hs
  linarith

end OperatorDerivativeRewrite.Foundation.CoerciveSchurStability
