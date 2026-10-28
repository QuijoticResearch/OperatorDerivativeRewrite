import Foundation.SU2SignBottleneck
noncomputable section
open scoped Quaternion
open OperatorDerivativeRewrite.Foundation.QuaternionSU2Representation
namespace OperatorDerivativeRewrite.Foundation.SU2WilsonSignCrossing

def circle (a b : ℝ) (h : a^2+b^2=1) : QuaternionAngularHaar.Group :=
  ⟨(⟨a,b,0,0⟩ : ℍ), by
    have hn : Quaternion.normSq (⟨a,b,0,0⟩ : ℍ) = 1 := by
      simpa [Quaternion.normSq_def', pow_two] using h
    rw [Unitary.mem_iff]
    constructor
    · rw [Quaternion.star_mul_self, hn]; rfl
    · rw [Quaternion.self_mul_star, hn]; rfl⟩

def left (a b : ℝ) (h : a^2+b^2=1) : SU2 := hom (circle a b h)
def right (a b : ℝ) (h : a^2+b^2=1) : SU2 := hom (circle (-a) b (by nlinarith))

theorem left_trace (a b : ℝ) (h : a^2+b^2=1) : halfTrace (left a b h) = a := by
  rw [left, halfTrace_map]
  rfl

theorem right_trace (a b : ℝ) (h : a^2+b^2=1) : halfTrace (right a b h) = -a := by
  rw [right, halfTrace_map]
  rfl

theorem relative_trace (a b : ℝ) (h : a^2+b^2=1) :
    halfTrace (left a b h * (right a b h)⁻¹) = 1-2*a^2 := by
  unfold left right
  rw [← map_inv, ← map_mul, halfTrace_map]
  change (((circle a b h * (circle (-a) b _)⁻¹ : QuaternionAngularHaar.Group) : ℍ).re) = _
  rw [← Unitary.star_eq_inv]
  simp only [Submonoid.coe_mul, Unitary.coe_star]
  change ((⟨a,b,0,0⟩ : ℍ) * star (⟨-a,b,0,0⟩ : ℍ)).re = _
  simp only [Quaternion.re_mul]
  dsimp
  nlinarith

def action (C D : SU2) : ℝ := 1-halfTrace (C*D⁻¹)

theorem crossing_action (a b : ℝ) (h : a^2+b^2=1) :
    action (left a b h) (right a b h) = 2*a^2 := by
  rw [action, relative_trace]
  ring

/-- Opposite trace signs do not force any positive temporal Wilson action barrier. -/
theorem arbitrarily_small_crossing (ε : ℝ) (hε : 0 < ε) :
    ∃ C D : SU2, 0 < halfTrace C ∧ halfTrace D < 0 ∧
      0 ≤ action C D ∧ action C D < ε := by
  let a := min (1/2 : ℝ) (Real.sqrt ε / 2)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha₁ : a ≤ 1/2 := min_le_left _ _
  have ha₂ : a ≤ Real.sqrt ε / 2 := min_le_right _ _
  have hs : (Real.sqrt ε)^2 = ε := Real.sq_sqrt hε.le
  have hspos := Real.sqrt_nonneg ε
  have hb : 0 ≤ 1-a^2 := by nlinarith
  let b := Real.sqrt (1-a^2)
  have hab : a^2+b^2=1 := by dsimp [b]; rw [Real.sq_sqrt hb]; ring
  refine ⟨left a b hab, right a b hab, ?_, ?_, ?_, ?_⟩
  · rw [left_trace]; exact ha
  · rw [right_trace]; linarith
  · rw [crossing_action]; positivity
  · rw [crossing_action]
    nlinarith


theorem relative_trace_can_exceed (q : ℝ) (hq : q < 1) :
    ∃ C D : SU2, 0 < halfTrace C ∧ halfTrace D < 0 ∧ q < halfTrace (C*D⁻¹) := by
  obtain ⟨C,D,hC,hD,_,hA⟩ := arbitrarily_small_crossing (1-q) (by linarith)
  exact ⟨C,D,hC,hD,by dsimp [action] at hA; linarith⟩

theorem no_positive_crossing_barrier :
    ¬∃ c : ℝ, 0 < c ∧ ∀ C D : SU2,
      0 < halfTrace C → halfTrace D < 0 → c ≤ action C D := by
  rintro ⟨c,hc,h⟩
  obtain ⟨C,D,hC,hD,_,hA⟩ := arbitrarily_small_crossing c hc
  exact (not_lt_of_ge (h C D hC hD)) hA

/-- At any fixed nonnegative inverse temperature, sign crossing can retain weight
arbitrarily close to the maximal temporal Wilson weight. This is pointwise only. -/
theorem crossing_weight_near_max (β η : ℝ) (hβ : 0 ≤ β) (hη : 0 < η) :
    ∃ C D : SU2, 0 < halfTrace C ∧ halfTrace D < 0 ∧
      Real.exp (-η) < Real.exp (-β * action C D) := by
  have hp : 0 < β+1 := by linarith
  obtain ⟨C,D,hC,hD,hA0,hA⟩ := arbitrarily_small_crossing (η/(β+1)) (div_pos hη hp)
  refine ⟨C,D,hC,hD,Real.exp_lt_exp.mpr ?_⟩
  have h := (lt_div_iff₀ hp).mp hA
  nlinarith

theorem action_conjugate (U C D : SU2) :
    action (U*C*U⁻¹) (U*D*U⁻¹) = action C D := by
  unfold action
  have he : (U*C*U⁻¹)*(U*D*U⁻¹)⁻¹ = U*(C*D⁻¹)*U⁻¹ := by group
  rw [he, halfTrace_conjugate]

/-- Homogeneous commuting spatial links. The flatness statement below is local
plaquette algebra, not a construction of an infinite-volume gauge measure. -/
def flatSlice (C : SU2) : Fin 3 → SU2 := ![C,1,1]

theorem flatSlice_plaquette (C : SU2) (i j : Fin 3) :
    flatSlice C i * flatSlice C j * (flatSlice C i)⁻¹ * (flatSlice C j)⁻¹ = 1 := by
  fin_cases i <;> fin_cases j <;> simp [flatSlice, mul_assoc]

theorem flatSlice_temporal_sum (C D : SU2) :
    (∑ i : Fin 3, action (flatSlice C i) (flatSlice D i)) = action C D := by
  simp [flatSlice, Fin.sum_univ_succ, action, SU2OpenLinkGaugeObstruction.halfTrace_one]
  ring


/-- The temporal Wilson action respects the full common endpoint gauge action. -/
theorem action_endpointGauge (g h C D : SU2) :
    action (g*C*h⁻¹) (g*D*h⁻¹) = action C D := by
  unfold action
  have he : (g*C*h⁻¹)*(g*D*h⁻¹)⁻¹ = g*(C*D⁻¹)*g⁻¹ := by group
  rw [he, halfTrace_conjugate]

/-- The same endpoint gauge transformation can remove opposite bare-link trace
signs without changing the Wilson action. Closed-loop holonomies are different. -/
theorem openLink_sign_cut_not_gauge_invariant :
    ∃ C D g : SU2, 0 < halfTrace C ∧ halfTrace D < 0 ∧
      0 < halfTrace (g*C) ∧ 0 < halfTrace (g*D) ∧ action (g*C) (g*D) = action C D := by
  have h : (3/5:ℝ)^2+(4/5:ℝ)^2=1 := by norm_num
  let C := left (3/5) (4/5) h
  let D := right (3/5) (4/5) h
  have hrel : halfTrace (C⁻¹*D) = (7/25:ℝ) := by
    dsimp [C,D,left,right]
    rw [← map_inv, ← map_mul, halfTrace_map]
    change (((circle (3/5) (4/5) h)⁻¹ * circle (-(3/5)) (4/5) _ : QuaternionAngularHaar.Group) : ℍ).re = _
    rw [← Unitary.star_eq_inv]
    simp only [Submonoid.coe_mul, Unitary.coe_star]
    norm_num [circle, Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
      Quaternion.imJ_star, Quaternion.imK_star]
  refine ⟨C,D,C⁻¹,?_,?_,?_,?_,?_⟩
  · dsimp [C]; rw [left_trace]; norm_num
  · dsimp [D]; rw [right_trace]; norm_num
  · simp [SU2OpenLinkGaugeObstruction.halfTrace_one]
  · rw [hrel]; norm_num
  · simpa using action_endpointGauge C⁻¹ 1 C D

end OperatorDerivativeRewrite.Foundation.SU2WilsonSignCrossing
