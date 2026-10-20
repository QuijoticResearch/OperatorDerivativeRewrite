import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Foundation.RealRootedLaguerreLimit

/-! A focused part of the subquadratic factorization problem: an even,
zero-free entire function with the quartic flow's growth bound is constant.
This does not construct the product of zeros or polynomial approximants. -/
noncomputable section
open Set Metric Filter Complex Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.EvenEntireZeroFreeRigidity

theorem exists_entire_log (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, Complex.exp (g z) = f z := by
  have hsc : IsSimplyConnected (univ : Set ℂ) := by
    letI : ContractibleSpace (univ : Set ℂ) :=
      (convex_univ : Convex ℝ (univ : Set ℂ)).contractibleSpace univ_nonempty
    exact SimplyConnectedSpace.ofContractible _
  obtain ⟨g,hgc,hg⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc isOpen_univ
    hf.continuous.continuousOn (by simpa using hne)
  have he (z : ℂ) : Complex.exp (g z) = f z := hg (mem_univ z)
  refine ⟨g,fun z => ?_,he⟩
  exact (HasDerivAt.of_comp_left
    (continuousOn_univ.mp hgc).continuousAt (Complex.hasDerivAt_exp (g z))
    (hf z).hasDerivAt (Complex.exp_ne_zero _) (Eventually.of_forall he)).differentiableAt

theorem zero_of_zero_derivative_and_subquadratic_real_part
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (h0 : g 0 = 0) (hd0 : deriv g 0 = 0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hbound : ∀ z, (g z).re ≤ A + B * (‖z‖ * Real.sqrt ‖z‖)) :
    ∀ z, g z = 0 := by
  have hlittle : (fun w : ℂ => g w - g 0) =o[𝓝 0] (fun w => ‖w - 0‖ ^ (1 : ℕ)) := by
    simpa only [hd0, smul_zero, sub_zero, pow_one] using
      ((hg 0).hasDerivAt.isLittleO.norm_right)
  intro z
  have hest : ∀ᶠ y : ℝ in atTop,
      ‖g z‖ ≤ (2 * (A + 4*B + 1) * ‖z‖^2) / y := by
    filter_upwards [eventually_ge_atTop (max 1 (‖z‖+1))] with y hy
    have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
    have hyp : 0 < y := by linarith
    have hyr : ‖z‖ < y^2 := by
      have := (le_max_right 1 (‖z‖+1)).trans hy
      nlinarith [norm_nonneg z]
    let M : ℝ := A + 4*B*y^3 + 1
    have hM : 0 < M := by dsimp [M]; positivity
    have hreal : MapsTo g (ball 0 (2*y^2)) {w | w.re ≤ M} := by
      intro w hw
      have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
      have hwr : ‖w‖ ≤ 2*y^2 := (mem_ball_zero_iff.mp hw).le
      have hs : Real.sqrt ‖w‖ ≤ 2*y := by
        apply (Real.sqrt_le_iff).mpr
        constructor
        · positivity
        · nlinarith
      have hp : ‖w‖ * Real.sqrt ‖w‖ ≤ 4*y^3 := by
        calc
          _ ≤ (2*y^2)*(2*y) := mul_le_mul hwr hs (Real.sqrt_nonneg _) (by positivity)
          _ = _ := by ring
      have := mul_le_mul_of_nonneg_left hp hB
      have := hbound w
      dsimp [M]
      change (g w).re ≤ _
      linarith
    have hmaps : MapsTo g (ball 0 (y^2)) (closedBall (g 0) (2*M)) := by
      intro w hw
      have hwr := mem_ball_zero_iff.mp hw
      have hw2 : w ∈ ball 0 (2*y^2) := mem_ball_zero_iff.mpr (by nlinarith)
      have hb := Complex.borelCaratheodory_zero hM hg.differentiableOn hreal
        (by positivity : 0 < 2*y^2) hw2 h0
      rw [mem_closedBall, dist_eq_norm, h0, sub_zero]
      apply hb.trans
      apply (div_le_iff₀ (by nlinarith : 0 < 2*y^2 - ‖w‖)).mpr
      nlinarith
    have hh := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      hg.differentiableOn hmaps hlittle (mem_ball_zero_iff.mpr hyr)
    simp only [h0, dist_zero_right] at hh
    apply hh.trans
    have hy3 : 1 ≤ y^3 := one_le_pow₀ hy1
    have hnum : M ≤ (A+4*B+1)*y^3 := by
      dsimp [M]
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hy3)]
    have hpos : 0 < y^2 := sq_pos_of_pos hyp
    calc
      2*M*(‖z‖/y^2)^2 ≤ 2*((A+4*B+1)*y^3)*(‖z‖/y^2)^2 := by gcongr
      _ = (2*(A+4*B+1)*‖z‖^2)/y := by field_simp
  have hlim : Tendsto (fun y : ℝ => (2*(A+4*B+1)*‖z‖^2)/y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_eq_zero.mp (le_antisymm (ge_of_tendsto hlim hest) (norm_nonneg _))

theorem even_zero_free_constant (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (heven : ∀ z, f (-z) = f z) (hne : ∀ z, f z ≠ 0)
    (C : ℝ) (hC : 0 < C)
    (hbound : ∀ z, ‖f z‖ ≤ C * Real.exp (‖z‖ * Real.sqrt ‖z‖)) :
    ∀ z, f z = f 0 := by
  obtain ⟨h,hh,hexp⟩ := exists_entire_log f hf hne
  let g : ℂ → ℂ := fun z => h z - h 0
  have hg : Differentiable ℂ g := hh.sub_const _
  have h0 : g 0 = 0 := sub_self _
  have hf0 : deriv f 0 = 0 := by
    have hd := ((hf (-(0 : ℂ))).hasDerivAt.comp (h := fun z : ℂ => -z)
      0 (hasDerivAt_neg (0 : ℂ))).deriv
    have he : (fun z : ℂ => f (-z)) = f := funext heven
    change deriv (fun z : ℂ => f (-z)) 0 = deriv f (-0) * -1 at hd
    rw [he,neg_zero] at hd
    linear_combination hd / 2
  have hgn (z : ℂ) : Complex.exp (g z) = f z / f 0 := by
    simp only [g,Complex.exp_sub,hexp]
  have hgd : HasDerivAt g (deriv f 0 / f 0) 0 := by
    have hex := (Complex.hasDerivAt_exp (g 0)).comp 0 (hg 0).hasDerivAt
    change HasDerivAt (fun z : ℂ => Complex.exp (g z)) _ 0 at hex
    have he : (fun z => Complex.exp (g z)) = fun z => f z / f 0 := funext hgn
    rw [he] at hex
    have hh' := ((hf 0).hasDerivAt.div_const (f 0)).deriv
    have hd := hex.deriv
    simp only [h0,Complex.exp_zero,one_mul] at hd
    rw [hd] at hh'
    simpa only [hh'] using (hg 0).hasDerivAt
  have hd0 : deriv g 0 = 0 := by rw [hgd.deriv,hf0,zero_div]
  let A := |Real.log C| + |Real.log ‖f 0‖| + 1
  have hb (z : ℂ) : (g z).re ≤ A + 1 * (‖z‖ * Real.sqrt ‖z‖) := by
    have hn : 0 < ‖f 0‖ := norm_pos_iff.mpr (hne 0)
    have hx : 0 < ‖f z‖ := norm_pos_iff.mpr (hne z)
    have he := congrArg norm (hgn z)
    rw [Complex.norm_exp,norm_div] at he
    have hlog := Real.log_le_log hx (hbound z)
    rw [Real.log_mul (ne_of_gt hC) (Real.exp_ne_zero _),Real.log_exp] at hlog
    have hl := congrArg Real.log he
    rw [Real.log_exp,Real.log_div (ne_of_gt hx) (ne_of_gt hn)] at hl
    dsimp [A]
    linarith [le_abs_self (Real.log C),neg_le_abs (Real.log ‖f 0‖)]
  have hz := zero_of_zero_derivative_and_subquadratic_real_part g hg h0 hd0 A 1
    (by dsimp [A]; positivity) (by norm_num) hb
  intro z
  have hv := hgn z
  rw [hz z,Complex.exp_zero] at hv
  exact (div_eq_one_iff_eq (hne 0)).mp hv.symm

/-- The strict growth restriction is essential: exp(z²) has no zeros at
all, but is not a locally uniform limit of split real polynomials. -/
theorem quadratic_zero_free_counterexample :
    ∃ f : ℂ → ℂ, Differentiable ℂ f ∧ (∀ z, f (-z) = f z) ∧
      (∀ z, f z ≠ 0) ∧ f 0 = 1 ∧
      (∀ z, ‖f z‖ ≤ Real.exp (‖z‖^2)) ∧
      ¬ ∃ P : ℕ → ℝ[X], (∀ n, (P n).Splits) ∧
        TendstoLocallyUniformlyOn
          (fun n z => ((P n).map (algebraMap ℝ ℂ)).eval z) f atTop univ := by
  let f : ℂ → ℂ := fun z => Complex.exp (z^2)
  have hd (z : ℂ) : HasDerivAt f (2*z*Complex.exp (z^2)) z := by
    convert (hasDerivAt_pow 2 z).cexp using 1 <;> simp [f] <;> ring
  have hd1 : deriv f = fun z => 2*z*Complex.exp (z^2) := funext fun z => (hd z).deriv
  have hd2 : deriv (deriv f) 0 = 2 := by
    rw [hd1]
    have h := (((hasDerivAt_id (0 : ℂ)).const_mul 2).mul (hd 0)).deriv
    change deriv (fun z : ℂ => 2*z*Complex.exp (z^2)) 0 = _ at h
    simpa only [f,id_eq,zero_pow (by norm_num : 2 ≠ 0),Complex.exp_zero,
      mul_zero,mul_one,add_zero] using h
  refine ⟨f,fun z => (hd z).differentiableAt,?_,fun z => Complex.exp_ne_zero _,
    by simp [f],?_,?_⟩
  · intro z
    simp [f]
  · intro z
    change ‖Complex.exp (z^2)‖ ≤ _
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    exact (Complex.re_le_norm (z^2)).trans_eq (_root_.norm_pow z 2)
  · rintro ⟨P,hP,hlim⟩
    have h := RealRootedLaguerreLimit.laguerre_nonneg_of_locally_uniform_split_polynomials_on
      P f univ isOpen_univ hP hlim 0 (mem_univ _)
    simp only [Complex.ofReal_zero] at h
    rw [hd2,hd1] at h
    norm_num [f] at h

end OperatorDerivativeRewrite.Foundation.EvenEntireZeroFreeRigidity
