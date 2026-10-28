import Foundation.SU2SevenLinkTransfer
import Mathlib.Analysis.Normed.Algebra.QuaternionExponential

/-! Joint link coordinates of a genuine SU2 plaquette need not be even,
although the Wilson action of a single exponential coordinate is even. -/
noncomputable section
open scoped Quaternion
namespace OperatorDerivativeRewrite.Foundation.SU2JointPlaquetteCubic
open QuaternionSU2Representation SU2SevenLinkTransfer

def axisRaw (a : Fin 3) (t : ℝ) : ℍ :=
  if a=0 then ⟨Real.cos t,Real.sin t,0,0⟩ else
    if a=1 then ⟨Real.cos t,0,Real.sin t,0⟩ else ⟨Real.cos t,0,0,Real.sin t⟩

theorem axisRaw_normSq (a : Fin 3) (t : ℝ) : Quaternion.normSq (axisRaw a t)=1 := by
  fin_cases a <;> norm_num [axisRaw,Quaternion.normSq_def'] <;>
    nlinarith [Real.sin_sq_add_cos_sq t]

def axis (a : Fin 3) (t : ℝ) : SU2 := hom ⟨axisRaw a t,by
  rw [Unitary.mem_iff]
  constructor
  · rw [Quaternion.star_mul_self,axisRaw_normSq]; rfl
  · rw [Quaternion.self_mul_star,axisRaw_normSq]; rfl⟩

def generatorRaw (a : Fin 3) : ℍ :=
  if a=0 then ⟨0,1,0,0⟩ else if a=1 then ⟨0,0,1,0⟩ else ⟨0,0,0,1⟩

theorem generatorRaw_norm (a : Fin 3) : ‖generatorRaw a‖=1 := by
  have he : Quaternion.normSq (generatorRaw a)=1 := by
    fin_cases a <;> norm_num [generatorRaw,Quaternion.normSq_def']
  rw [Quaternion.normSq_eq_norm_mul_self] at he
  nlinarith [norm_nonneg (generatorRaw a)]

/-- The link curves are actual imaginary-quaternion exponentials, not a
polynomial or finite-group proxy for SU2. -/
theorem axisRaw_exp (a : Fin 3) (t : ℝ) :
    NormedSpace.exp (t • generatorRaw a)=axisRaw a t := by
  have hr : (t • generatorRaw a).re=0 := by fin_cases a <;> simp [generatorRaw]
  have hn : ‖t • generatorRaw a‖=|t| := by
    rw [norm_smul,generatorRaw_norm,mul_one,Real.norm_eq_abs]
  rw [Quaternion.exp_of_re_eq_zero _ hr,hn]
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rw [abs_of_neg ht,Real.cos_neg,Real.sin_neg]
    fin_cases a <;> ext <;> simp [generatorRaw,axisRaw] <;> field_simp [ht.ne] <;> ring
  · subst t
    fin_cases a <;> ext <;> norm_num [generatorRaw,axisRaw]
  · rw [abs_of_pos ht]
    fin_cases a <;> ext <;> simp [generatorRaw,axisRaw] <;> field_simp [ht.ne'] <;> ring

def configuration (x y z : ℝ) : State := (1,axis 0 x,axis 1 y,axis 2 z,1,1,1)

def action (x y z : ℝ) : ℝ := 1-first (configuration x y z)

theorem action_formula (x y z : ℝ) :
    action x y z=1-Real.cos x*Real.cos y*Real.cos z+Real.sin x*Real.sin y*Real.sin z := by
  change 1-halfTrace (axis 0 x*axis 1 y*axis 2 z*1)=_
  rw [mul_one]
  unfold axis
  rw [← hom.map_mul,← hom.map_mul]
  change 1-(SU2TraceHessianModel.traceReal (repr ((axisRaw 0 x*axisRaw 1 y)*axisRaw 2 z))/2)=_
  rw [repr_halfTrace]
  norm_num [axisRaw,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
  ring

theorem action_gauge (x y z : ℝ) (g : Fin 6 → SU2) :
    1-first (gaugeAction g (configuration x y z))=action x y z := by
  rw [first_gauge]
  rfl

theorem action_x_hasDerivAt (x y z : ℝ) :
    HasDerivAt (fun s => action s y z)
      (Real.sin x*Real.cos y*Real.cos z+Real.cos x*Real.sin y*Real.sin z) x := by
  have he : (fun s => action s y z)=(fun s =>
      1-Real.cos s*Real.cos y*Real.cos z+Real.sin s*Real.sin y*Real.sin z) :=
    funext (fun s => action_formula s y z)
  rw [he]
  convert ((hasDerivAt_const x (1:ℝ)).sub
    (((Real.hasDerivAt_cos x).mul_const (Real.cos y)).mul_const (Real.cos z))).add
    (((Real.hasDerivAt_sin x).mul_const (Real.sin y)).mul_const (Real.sin z)) using 1 <;> ring

theorem mixed_hessian (z : ℝ) :
    deriv (fun y : ℝ => deriv (fun x : ℝ => action x y z) 0) 0=Real.sin z := by
  have he : (fun y : ℝ => deriv (fun x : ℝ => action x y z) 0)=
      (fun y => Real.sin y*Real.sin z) := by
    funext y
    rw [(action_x_hasDerivAt 0 y z).deriv]
    simp
  rw [he]
  simpa using ((Real.hasDerivAt_sin 0).mul_const (Real.sin z)).deriv

/-- A nonzero joint third derivative at the all-identity configuration. -/
theorem mixed_third_at_identity :
    deriv (fun z : ℝ => deriv (fun y : ℝ => deriv (fun x : ℝ => action x y z) 0) 0) 0=1 := by
  simp_rw [mixed_hessian]
  simpa using (Real.hasDerivAt_sin 0).deriv

theorem odd_part (t : ℝ) : action t t t-action (-t) (-t) (-t)=2*Real.sin t^3 := by
  rw [action_formula,action_formula]
  simp only [Real.cos_neg,Real.sin_neg]
  ring

theorem no_quadratic_mixed_hessian_bound :
    ¬ ∃ K ε : ℝ, 0 ≤ K ∧ 0 < ε ∧ ∀ z : ℝ, 0 < z → z < ε →
      |deriv (fun y : ℝ => deriv (fun x : ℝ => action x y z) 0) 0| ≤ K*z^2 := by
  rintro ⟨K,ε,hK,hε,hb⟩
  apply SU2OrderedLinkHessian.no_local_quadratic_bound
  refine ⟨K,ε,hK,hε,?_⟩
  intro z hz hzε
  have he := hb z hz hzε
  rw [mixed_hessian] at he
  rw [SU2OrderedLinkHessian.correction_eq,abs_div,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith [abs_nonneg (Real.sin z)]

/-- The valid repair along this slice is linear, not quadratic, in the
remaining link angle. This is an exact bound, not a sharp global Hessian claim. -/
theorem mixed_hessian_linear_bound (z : ℝ) :
    |deriv (fun y : ℝ => deriv (fun x : ℝ => action x y z) 0) 0| ≤ |z| := by
  rw [mixed_hessian]
  exact Real.abs_sin_le_abs

theorem not_even_in_any_neighborhood (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 < t ∧ t < ε ∧ action t t t ≠ action (-t) (-t) (-t) := by
  obtain ⟨t,ht,htε,hc⟩ := SU2OrderedLinkHessian.correction_exceeds_quadratic 0 ε (by norm_num) hε
  rw [SU2OrderedLinkHessian.correction_eq] at hc
  have hs : 0 < Real.sin t := by nlinarith
  refine ⟨t,ht,htε,?_⟩
  intro he
  have ho := odd_part t
  rw [he,sub_self] at ho
  have hp : 0 < 2*Real.sin t^3 := by positivity
  linarith

def quadraticCore (x y z : ℝ) : ℝ := (x^2+y^2+z^2)/2

def remainder (x y z : ℝ) : ℝ := action x y z-quadraticCore x y z

theorem mixed_remainder_hessian (z : ℝ) :
    deriv (fun y : ℝ => deriv (fun x : ℝ => remainder x y z) 0) 0=Real.sin z := by
  have he (y : ℝ) : deriv (fun x : ℝ => remainder x y z) 0=
      deriv (fun x : ℝ => action x y z) 0 := by
    have hc : HasDerivAt (fun x : ℝ => quadraticCore x y z) 0 0 := by
      convert ((((hasDerivAt_id (0:ℝ)).pow 2).add_const (y^2)).add_const (z^2)).div_const 2 using 1 <;>
        simp [quadraticCore]
    change deriv ((fun x : ℝ => action x y z)-(fun x => quadraticCore x y z)) 0=_
    rw [deriv_sub (action_x_hasDerivAt 0 y z).differentiableAt hc.differentiableAt,hc.deriv,sub_zero]
  simp_rw [he]
  exact mixed_hessian z

/-- Even a coupling-independent O(1) allowance cannot repair a uniform
O(beta*delta^2) claim on a fixed small link-coordinate neighborhood. -/
theorem no_uniform_quadratic_plus_constant :
    ¬ ∃ C C0 ε : ℝ, 0 ≤ C ∧ 0 ≤ C0 ∧ 0 < ε ∧
      ∀ β z : ℝ, 1 ≤ β → 0 < z → z < ε →
        β*|deriv (fun y : ℝ => deriv (fun x : ℝ => remainder x y z) 0) 0| ≤ C*β*z^2+C0 := by
  rintro ⟨C,C0,ε,hC,hC0,hε,hb⟩
  obtain ⟨z,hz,hzε,hc⟩ := SU2OrderedLinkHessian.correction_exceeds_quadratic C ε hC hε
  rw [SU2OrderedLinkHessian.correction_eq] at hc
  let d := Real.sin z-C*z^2
  have hd : 0 < d := by dsimp [d]; nlinarith [mul_nonneg hC (sq_nonneg z)]
  let β := (C0+1)/d+1
  have hβ : 1 ≤ β := by
    have hp : 0 ≤ (C0+1)/d := div_nonneg (by linarith) hd.le
    dsimp [β]
    linarith
  have he := hb β z hβ hz hzε
  rw [mixed_remainder_hessian] at he
  have hm : β*d=C0+1+d := by dsimp [β]; field_simp [hd.ne'] <;> ring
  have hsin : β*Real.sin z ≤ β*|Real.sin z| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by linarith)
  dsimp [d] at hm hd
  nlinarith

/-- Along this slice, a quadratic-plus-constant budget forces an O(1/beta)
angle window. It does NOT deny a valid linear-in-angle estimate. -/
theorem budget_requires_inverse_coupling_window (β z C C0 : ℝ)
    (hβ : 0 < β) (hz : 0 ≤ z) (hz1 : z ≤ 1) (hC : 0 ≤ C)
    (hsmall : 4*C*z ≤ 1)
    (hb : β*|deriv (fun y : ℝ => deriv (fun x : ℝ => remainder x y z) 0) 0| ≤ C*β*z^2+C0) :
    β*z ≤ 4*C0 := by
  rw [mixed_remainder_hessian] at hb
  have hsq : z^2 ≤ 1 := by nlinarith
  have hcube : z^3 ≤ z := by nlinarith [mul_nonneg hz (sub_nonneg.mpr hsq)]
  have hsin : z/2 ≤ Real.sin z := by nlinarith [Real.sin_ge_sub_cube hz]
  have hquad : C*z^2 ≤ z/4 := by nlinarith [mul_nonneg hz (sub_nonneg.mpr hsmall)]
  have h1 := mul_le_mul_of_nonneg_left hsin hβ.le
  have h2 := mul_le_mul_of_nonneg_left hquad hβ.le
  have h3 := mul_le_mul_of_nonneg_left (le_abs_self (Real.sin z)) hβ.le
  nlinarith

/-- Failure already on an inverse-square-root coupling window: beta=s^2,
z=1/s, so beta*z^2=1 while the mixed Hessian grows like s. -/
theorem thermal_window_counterexample (C C0 R : ℝ) (hC : 0 ≤ C) (hC0 : 0 ≤ C0) :
    ∃ s : ℝ, R < s ∧ 1 < s ∧ C+C0 < s^2*
      |deriv (fun y : ℝ => deriv (fun x : ℝ => remainder x y (1/s)) 0) 0| := by
  let s := 4*C+4*C0+|R|+2
  have hR := abs_nonneg R
  have hsR : R < s := by dsimp [s]; linarith [le_abs_self R]
  have hs : 1 < s := by dsimp [s]; linarith
  have hsp : 0 < s := by linarith
  refine ⟨s,hsR,hs,?_⟩
  by_contra hnot
  have hb : s^2*|deriv (fun y : ℝ => deriv (fun x : ℝ => remainder x y (1/s)) 0) 0|
      ≤ C*s^2*(1/s)^2+C0 := by
    have hid : C*s^2*(1/s)^2=C := by field_simp <;> ring
    rw [hid]
    exact le_of_not_gt hnot
  have hz : (0:ℝ) ≤ 1/s := by positivity
  have hz1 : 1/s ≤ (1:ℝ) := (div_le_one hsp).mpr hs.le
  have hsmall : 4*C*(1/s) ≤ 1 := by
    rw [mul_one_div]
    apply (div_le_one hsp).mpr
    dsimp [s]
    linarith
  have he := budget_requires_inverse_coupling_window (s^2) (1/s) C C0
    (sq_pos_of_pos hsp) hz hz1 hC hsmall hb
  have hid : s^2*(1/s)=s := by field_simp <;> ring
  rw [hid] at he
  dsimp [s] at he
  linarith

theorem diagonal_hessian (z : ℝ) :
    deriv (deriv (fun x : ℝ => action x 0 z)) 0=Real.cos z := by
  have he : deriv (fun x : ℝ => action x 0 z)=(fun x => Real.sin x*Real.cos z) := by
    funext x
    rw [(action_x_hasDerivAt x 0 z).deriv]
    simp
  rw [he]
  simpa using ((Real.hasDerivAt_sin 0).mul_const (Real.cos z)).deriv

theorem action_symmetric_xy (x y z : ℝ) : action x y z=action y x z := by
  rw [action_formula,action_formula]
  ring

/-- The scalar Schur complement of the actual (x,y) Hessian on this slice:
both diagonal entries are cos z and the off-diagonal entry is sin z. -/
def schurSlice (z : ℝ) : ℝ := Real.cos z-(Real.sin z)^2/Real.cos z

/-- Squaring the CORRECT linear mixed term still gives a quadratic Schur loss.
This slice estimate is not a global lattice curvature or mass gap. -/
theorem schurSlice_lower (z : ℝ) (hcos : 1/2 ≤ Real.cos z) :
    1-(5/2:ℝ)*z^2 ≤ schurSlice z := by
  have hp : 0 < Real.cos z := by linarith
  have hs : Real.sin z^2 ≤ z^2 := Real.sin_sq_le_sq
  have hdiv : Real.sin z^2/Real.cos z ≤ 2*z^2 := by
    apply (div_le_iff₀ hp).mpr
    have hm := mul_le_mul_of_nonneg_right hcos (sq_nonneg z)
    nlinarith
  have hc := Real.one_sub_sq_div_two_le_cos (x := z)
  unfold schurSlice
  linarith

end OperatorDerivativeRewrite.Foundation.SU2JointPlaquetteCubic
