import Foundation.CoerciveSchurStability
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-! A varying-interior Schur comparison retaining the nonzero-reference cross
term. Interior solutions and coercivity replace an assumed inverse-norm bound. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.VaryingSchurStability
open CoerciveSchurStability
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def solvedSchur (a : ℝ) (b u : E) : ℝ := a-inner ℝ b u

theorem completed_square (C : E →L[ℝ] E) (a x : ℝ) (b u y : E)
    (hSym : C.toLinearMap.IsSymmetric) (hu : C u=b) :
    blockEnergy a b (fun z => inner ℝ (C z) z) x y=
      solvedSchur a b u*x^2+inner ℝ (C (y+x • u)) (y+x • u) := by
  have hs : inner ℝ (C y) u=inner ℝ b y := by
    calc
      _ = inner ℝ y (C u) := hSym _ _
      _ = _ := by rw [hu,real_inner_comm]
  unfold blockEnergy solvedSchur
  simp only [map_add,map_smul,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,hu]
  rw [hs]
  ring

/-- The solved scalar Schur quantity is the attained eliminated quadratic energy. -/
theorem attained_reduction (C : E →L[ℝ] E) (a x c : ℝ) (b u : E)
    (hc : 0 < c) (hSym : C.toLinearMap.IsSymmetric) (hu : C u=b)
    (hC : ∀ y, c*‖y‖^2 ≤ inner ℝ (C y) y) :
    (∀ y, solvedSchur a b u*x^2 ≤ blockEnergy a b (fun z => inner ℝ (C z) z) x y) ∧
      blockEnergy a b (fun z => inner ℝ (C z) z) x ((-x) • u)=solvedSchur a b u*x^2 := by
  constructor
  · intro y
    rw [completed_square C a x b u y hSym hu]
    apply le_add_of_nonneg_right
    exact (mul_nonneg hc.le (sq_nonneg _)).trans (hC _)
  · rw [completed_square C a x b u ((-x) • u) hSym hu]
    simp

theorem coercive_norm_bound (C : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hC : ∀ y, c*‖y‖^2 ≤ inner ℝ (C y) y) (u : E) : ‖u‖ ≤ ‖C u‖/c := by
  by_cases hu : u=0
  · simp [hu]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hi := (hC u).trans (real_inner_le_norm (C u) u)
  apply (le_div_iff₀ hc).mpr
  apply (mul_le_mul_iff_right₀ hn).mp
  nlinarith

theorem half_coercivity (C C0 : E →L[ℝ] E) (m η : ℝ)
    (hη : η ≤ m/2) (hC0 : ∀ y, m*‖y‖^2 ≤ inner ℝ (C0 y) y)
    (hpert : ‖C-C0‖ ≤ η) (y : E) :
    (m/2)*‖y‖^2 ≤ inner ℝ (C y) y := by
  have hp := operator_quadratic_perturbation C C0 η hpert y
  have hs := mul_le_mul_of_nonneg_right hη (sq_nonneg ‖y‖)
  nlinarith [hC0 y]

/-- Exact comparison, including the first-order coupling contribution. -/
theorem solved_increment (C : E →L[ℝ] E) (b b0 u u0 v : E)
    (hSym : C.toLinearMap.IsSymmetric) (hu : C u=b) (hv : C v=b0) :
    inner ℝ b u-inner ℝ b0 u0=
      inner ℝ (b-b0) (u-v)+2*inner ℝ (b-b0) v+inner ℝ b0 (v-u0) := by
  have hw : C (u-v)=b-b0 := by rw [map_sub,hu,hv]
  have hx : inner ℝ (b-b0) v=inner ℝ b0 (u-v) := by
    rw [← hw]
    calc
      _ = inner ℝ (u-v) (C v) := hSym _ _
      _ = _ := by rw [hv,real_inner_comm]
  simp only [inner_sub_left,inner_sub_right] at hx ⊢
  linarith

theorem interior_solution_difference (C C0 : E →L[ℝ] E) (b0 v u0 : E)
    (c c0 η : ℝ) (hc : 0 < c) (hc0 : 0 < c0)
    (hC : ∀ y, c*‖y‖^2 ≤ inner ℝ (C y) y)
    (hC0 : ∀ y, c0*‖y‖^2 ≤ inner ℝ (C0 y) y)
    (hpert : ‖C-C0‖ ≤ η) (hv : C v=b0) (hu0 : C0 u0=b0) :
    ‖v-u0‖ ≤ η*‖b0‖/(c*c0) := by
  have hη : 0 ≤ η := (norm_nonneg (C-C0)).trans hpert
  have hn0 : ‖u0‖ ≤ ‖b0‖/c0 := by
    simpa only [hu0] using coercive_norm_bound C0 c0 hc0 hC0 u0
  have he : C (v-u0)=-((C-C0) u0) := by
    simp only [map_sub,ContinuousLinearMap.sub_apply,hv,hu0]
    abel
  have hr : ‖C (v-u0)‖ ≤ η*‖u0‖ := by
    rw [he,norm_neg]
    exact ((C-C0).le_opNorm u0).trans
      (mul_le_mul_of_nonneg_right hpert (norm_nonneg u0))
  calc
    _ ≤ ‖C (v-u0)‖/c := coercive_norm_bound C c hc hC (v-u0)
    _ ≤ (η*‖u0‖)/c := div_le_div_of_nonneg_right hr hc.le
    _ ≤ (η*(‖b0‖/c0))/c := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hn0 hη) hc.le
    _ = _ := by ring

/-- General positive-coercivity comparison for actual solved interior equations. -/
theorem solved_lower (C C0 : E →L[ℝ] E) (a a0 δ ε η c c0 : ℝ)
    (b b0 u u0 v : E) (hc : 0 < c) (hc0 : 0 < c0)
    (hSym : C.toLinearMap.IsSymmetric)
    (hC : ∀ y, c*‖y‖^2 ≤ inner ℝ (C y) y)
    (hC0 : ∀ y, c0*‖y‖^2 ≤ inner ℝ (C0 y) y)
    (ha : |a-a0| ≤ δ) (hb : ‖b-b0‖ ≤ ε) (hpert : ‖C-C0‖ ≤ η)
    (hu : C u=b) (hu0 : C0 u0=b0) (hv : C v=b0) :
    solvedSchur a0 b0 u0-δ-(ε^2+2*ε*‖b0‖)/c-η*‖b0‖^2/(c*c0) ≤
      solvedSchur a b u := by
  have hε : 0 ≤ ε := (norm_nonneg (b-b0)).trans hb
  have hw : ‖u-v‖ ≤ ε/c := by
    have he : C (u-v)=b-b0 := by rw [map_sub,hu,hv]
    calc
      _ ≤ ‖C (u-v)‖/c := coercive_norm_bound C c hc hC (u-v)
      _ = ‖b-b0‖/c := by rw [he]
      _ ≤ _ := div_le_div_of_nonneg_right hb hc.le
  have hvn : ‖v‖ ≤ ‖b0‖/c := by
    simpa only [hv] using coercive_norm_bound C c hc hC v
  have hr := interior_solution_difference C C0 b0 v u0 c c0 η hc hc0 hC hC0 hpert hv hu0
  have hi1 : inner ℝ (b-b0) (u-v) ≤ ε*(ε/c) :=
    (real_inner_le_norm _ _).trans (mul_le_mul hb hw (norm_nonneg _) hε)
  have hi2 : inner ℝ (b-b0) v ≤ ε*(‖b0‖/c) :=
    (real_inner_le_norm _ _).trans (mul_le_mul hb hvn (norm_nonneg _) hε)
  have hi3 : inner ℝ b0 (v-u0) ≤ ‖b0‖*(η*‖b0‖/(c*c0)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
  have hs : inner ℝ b u-inner ℝ b0 u0 ≤
      (ε^2+2*ε*‖b0‖)/c+η*‖b0‖^2/(c*c0) := by
    rw [solved_increment C b b0 u u0 v hSym hu hv]
    calc
      _ ≤ ε*(ε/c)+2*(ε*(‖b0‖/c))+‖b0‖*(η*‖b0‖/(c*c0)) := by linarith
      _ = _ := by ring
  unfold solvedSchur
  linarith [neg_le_of_abs_le ha]

/-- In finite dimension, coercivity supplies the auxiliary interior solution. -/
theorem finite_solved_lower [FiniteDimensional ℝ E]
    (C C0 : E →L[ℝ] E) (a a0 δ ε η c c0 : ℝ) (b b0 u u0 : E)
    (hc : 0 < c) (hc0 : 0 < c0) (hSym : C.toLinearMap.IsSymmetric)
    (hC : ∀ y, c*‖y‖^2 ≤ inner ℝ (C y) y)
    (hC0 : ∀ y, c0*‖y‖^2 ≤ inner ℝ (C0 y) y)
    (ha : |a-a0| ≤ δ) (hb : ‖b-b0‖ ≤ ε) (hpert : ‖C-C0‖ ≤ η)
    (hu : C u=b) (hu0 : C0 u0=b0) :
    solvedSchur a0 b0 u0-δ-(ε^2+2*ε*‖b0‖)/c-η*‖b0‖^2/(c*c0) ≤
      solvedSchur a b u := by
  obtain ⟨v,hv⟩ := finite_coercive_solution C c hc hC b0
  exact solved_lower C C0 a a0 δ ε η c c0 b b0 u u0 v hc hc0 hSym hC hC0 ha hb hpert hu hu0 hv

/-- The corrected corridor estimate with the source's half-coercivity constants. -/
theorem corridor_lower [FiniteDimensional ℝ E]
    (C C0 : E →L[ℝ] E) (a a0 δ ε η m : ℝ) (b b0 u u0 : E)
    (hm : 0 < m) (hη : η ≤ m/2) (hSym : C.toLinearMap.IsSymmetric)
    (hC0 : ∀ y, m*‖y‖^2 ≤ inner ℝ (C0 y) y)
    (ha : |a-a0| ≤ δ) (hb : ‖b-b0‖ ≤ ε) (hpert : ‖C-C0‖ ≤ η)
    (hu : C u=b) (hu0 : C0 u0=b0) :
    solvedSchur a0 b0 u0-δ-(2*ε^2+4*ε*‖b0‖)/m-2*η*‖b0‖^2/m^2 ≤
      solvedSchur a b u := by
  have hC := half_coercivity C C0 m η hη hC0 hpert
  have hs := finite_solved_lower C C0 a a0 δ ε η (m/2) m b b0 u u0
    (by positivity) hm hSym hC hC0 ha hb hpert hu hu0
  convert hs using 1 <;> ring

theorem corridor_solutions [FiniteDimensional ℝ E]
    (C C0 : E →L[ℝ] E) (a a0 δ ε η m : ℝ) (b b0 : E)
    (hm : 0 < m) (hη : η ≤ m/2) (hSym : C.toLinearMap.IsSymmetric)
    (hC0 : ∀ y, m*‖y‖^2 ≤ inner ℝ (C0 y) y)
    (ha : |a-a0| ≤ δ) (hb : ‖b-b0‖ ≤ ε) (hpert : ‖C-C0‖ ≤ η) :
    ∃ u u0, C u=b ∧ C0 u0=b0 ∧
      solvedSchur a0 b0 u0-δ-(2*ε^2+4*ε*‖b0‖)/m-2*η*‖b0‖^2/m^2 ≤
        solvedSchur a b u := by
  obtain ⟨u,hu⟩ := finite_coercive_solution C (m/2) (by positivity)
    (half_coercivity C C0 m η hη hC0 hpert) b
  obtain ⟨u0,hu0⟩ := finite_coercive_solution C0 m hm hC0 b0
  exact ⟨u,u0,hu,hu0,corridor_lower C C0 a a0 δ ε η m b b0 u u0
    hm hη hSym hC0 ha hb hpert hu hu0⟩

theorem corridor_energy_lower [FiniteDimensional ℝ E]
    (C C0 : E →L[ℝ] E) (a a0 δ ε η m : ℝ) (b b0 u0 : E)
    (hm : 0 < m) (hη : η ≤ m/2) (hSym : C.toLinearMap.IsSymmetric)
    (hC0 : ∀ y, m*‖y‖^2 ≤ inner ℝ (C0 y) y)
    (ha : |a-a0| ≤ δ) (hb : ‖b-b0‖ ≤ ε) (hpert : ‖C-C0‖ ≤ η)
    (hu0 : C0 u0=b0) (x : ℝ) (y : E) :
    (solvedSchur a0 b0 u0-δ-(2*ε^2+4*ε*‖b0‖)/m-2*η*‖b0‖^2/m^2)*x^2 ≤
      blockEnergy a b (fun z => inner ℝ (C z) z) x y := by
  have hC := half_coercivity C C0 m η hη hC0 hpert
  obtain ⟨u,hu⟩ := finite_coercive_solution C (m/2) (by positivity) hC b
  have hs := corridor_lower C C0 a a0 δ ε η m b b0 u u0
    hm hη hSym hC0 ha hb hpert hu hu0
  exact (mul_le_mul_of_nonneg_right hs (sq_nonneg x)).trans
    ((attained_reduction C a x (m/2) b u (by positivity) hSym hu hC).1 y)

end OperatorDerivativeRewrite.Foundation.VaryingSchurStability
