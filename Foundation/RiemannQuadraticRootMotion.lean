import Foundation.RiemannQuadraticConfinement
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Finite polynomial backward-heat root motion and an uppermost-branch barrier.
The derivative ratio is an exact root interaction sum. Conjugate pairing forces
an uppermost nonreal root downward. A genuine quartic heat branch through I moves
upward, so the uppermost hypothesis is essential. No global Xi transfer is assumed. -/
noncomputable section
open Polynomial Complex Finset Set Filter
open scoped Topology
open scoped ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticRootMotion

def rootPolynomial (S : Finset ℂ) : ℂ[X] := ∏ b ∈ S, (X-C b)

theorem eval_rootPolynomial (S : Finset ℂ) (z : ℂ) :
    (rootPolynomial S).eval z=∏ b ∈ S, (z-b) := by
  simp [rootPolynomial,eval_prod]

theorem logarithmic_product (S : Finset ℂ) (z : ℂ) (hz : z ∉ S) :
    (rootPolynomial S).derivative.eval z/(rootPolynomial S).eval z=
      ∑ b ∈ S, (z-b)⁻¹ := by
  have hn (b : ℂ) (hb : b ∈ S) : z-b ≠ 0 := sub_ne_zero.mpr (by
    intro he; subst b; exact hz hb)
  have he : (fun w => (rootPolynomial S).eval w)=(∏ b ∈ S, fun w : ℂ => w-b) := by
    funext w; simpa only [Finset.prod_apply] using eval_rootPolynomial S w
  have hd := logDeriv_prod (s:=S) (f:=fun b w : ℂ => w-b) (x:=z) hn
    (fun b _ => by fun_prop)
  have hre : logDeriv (fun w => (rootPolynomial S).eval w) z=
      (rootPolynomial S).derivative.eval z/(rootPolynomial S).eval z := by
    rw [logDeriv_apply,Polynomial.deriv]
  rw [← hre,he,hd]
  apply Finset.sum_congr rfl
  intro b hb
  simp [logDeriv_apply]

theorem root_derivative_ratio (S : Finset ℂ) (a : ℂ) (ha : a ∈ S) :
    (rootPolynomial S).derivative.derivative.eval a/(rootPolynomial S).derivative.eval a=
      2*∑ b ∈ S.erase a, (a-b)⁻¹ := by
  classical
  have he : rootPolynomial S=(X-C a)*rootPolynomial (S.erase a) := by
    exact (Finset.mul_prod_erase S (fun b : ℂ => (X-C b : ℂ[X])) ha).symm
  rw [he]
  simp only [derivative_mul,derivative_sub,derivative_X,derivative_C,
    sub_zero,one_mul,derivative_add,eval_add,eval_mul,eval_sub,eval_X,eval_C,
    sub_self,zero_mul,add_zero]
  rw [← logarithmic_product (S.erase a) a (Finset.notMem_erase a S)]
  ring

theorem root_derivative_ne_zero (S : Finset ℂ) (a : ℂ) (ha : a ∈ S) :
    (rootPolynomial S).derivative.eval a ≠ 0 := by
  classical
  have he : rootPolynomial S=(X-C a)*rootPolynomial (S.erase a) :=
    (Finset.mul_prod_erase S (fun b : ℂ => (X-C b : ℂ[X])) ha).symm
  rw [he]
  simp only [derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,
    one_mul,eval_add,eval_mul,eval_sub,eval_X,eval_C,sub_self,zero_mul,add_zero]
  rw [eval_rootPolynomial]
  exact Finset.prod_ne_zero_iff.mpr (fun b hb => sub_ne_zero.mpr
    (Ne.symm (Finset.mem_erase.mp hb).1))

theorem inverse_difference_im_nonpos (a b : ℂ) (hb : b.im ≤ a.im) :
    ((a-b)⁻¹).im ≤ 0 := by
  rw [Complex.inv_im,Complex.sub_im]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (Complex.normSq_nonneg _)

theorem conjugate_interaction (a : ℂ) (ha : 0<a.im) :
    (2*((a-conj a)⁻¹)).im= -1/a.im := by
  have hn : a.im ≠ 0 := ne_of_gt ha
  simp only [Complex.mul_im,show (2:ℂ).re=(2:ℝ) from rfl,
    show (2:ℂ).im=0 from rfl,zero_mul,add_zero,Complex.inv_im,Complex.sub_im,Complex.conj_im,
    Complex.normSq_apply,Complex.sub_re,Complex.conj_re,sub_self,mul_zero]
  field_simp
  ring

theorem uppermost_interaction (S : Finset ℂ) (a : ℂ)
    (ha : 0<a.im) (hc : conj a ∈ S) (hmax : ∀ b ∈ S, b.im ≤ a.im) :
    (2*∑ b ∈ S.erase a, (a-b)⁻¹).im ≤ -1/a.im := by
  classical
  have hne : conj a ≠ a := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.conj_im] at hi
    linarith
  have hmem : conj a ∈ S.erase a := Finset.mem_erase.mpr ⟨hne,hc⟩
  have hrest : (∑ b ∈ (S.erase a).erase (conj a), ((a-b)⁻¹).im) ≤ 0 :=
    Finset.sum_nonpos (fun b hb => inverse_difference_im_nonpos a b
      (hmax b (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hb))))
  have hs := Finset.add_sum_erase (S.erase a) (fun b : ℂ => ((a-b)⁻¹).im) hmem
  have hpair := conjugate_interaction a ha
  simp only [Complex.mul_im,show (2:ℂ).re=(2:ℝ) from rfl,
    show (2:ℂ).im=0 from rfl,zero_mul,add_zero,Complex.im_sum] at hpair ⊢
  linarith

theorem uppermost_polynomial_ratio (S : Finset ℂ) (a : ℂ) (ha : a ∈ S)
    (hi : 0<a.im) (hc : conj a ∈ S) (hmax : ∀ b ∈ S, b.im ≤ a.im) :
    ((rootPolynomial S).derivative.derivative.eval a/
      (rootPolynomial S).derivative.eval a).im ≤ -1/a.im := by
  rw [root_derivative_ratio S a ha]
  exact uppermost_interaction S a hi hc hmax

theorem heat_factor_velocity (P Q : ℝ → ℂ[X]) (r : ℝ → ℂ)
    (t : ℝ) (v qdot : ℂ)
    (hfactor : ∀ s, P s=(X-C (r s))*Q s)
    (hr : HasDerivAt r v t)
    (hq : HasDerivAt (fun s => (Q s).eval (r t)) qdot t)
    (hheat : HasDerivAt (fun s => (P s).eval (r t))
      (-(P t).derivative.derivative.eval (r t)) t)
    (hsimple : (P t).derivative.eval (r t) ≠ 0) :
    v=(P t).derivative.derivative.eval (r t)/(P t).derivative.eval (r t) := by
  have he : (P t).derivative.eval (r t)=(Q t).eval (r t) := by
    rw [hfactor t]
    simp
  have hfun : (fun s => (P s).eval (r t))=
      (fun s => (r t-r s)*(Q s).eval (r t)) := by
    funext s
    rw [hfactor s]
    simp
  have hd := ((hasDerivAt_const t (r t)).sub hr).mul hq
  simp only [Pi.sub_def,Pi.mul_def,zero_sub,sub_self,zero_mul,add_zero] at hd
  rw [← hfun] at hd
  have hv := hd.unique hheat
  apply (eq_div_iff hsimple).mpr
  rw [he]
  linear_combination -hv

theorem squared_height_derivative (r : ℝ → ℂ) (t : ℝ) (v : ℂ)
    (hr : HasDerivAt r v t) (hi : 0<(r t).im) (hv : v.im ≤ -1/(r t).im) :
    HasDerivAt (fun s => (r s).im^2) (2*(r t).im*v.im) t ∧
      2*(r t).im*v.im ≤ -2 := by
  have hd := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hr
  have hs := hd.pow 2
  have hineq := mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 2*(r t).im)
  have he : (2*(r t).im)*(-1/(r t).im)= -2 := by field_simp
  exact ⟨by simpa only [Pi.pow_def,Function.comp_def,Complex.imCLM_apply,Nat.reduceSub,pow_one,Nat.cast_ofNat] using hs,by linarith [he]⟩

theorem squared_height_barrier (y v : ℝ → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hy : ∀ u ∈ Icc s t, 0<y u)
    (hd : ∀ u ∈ Icc s t, HasDerivAt y (v u) u)
    (hv : ∀ u ∈ Icc s t, v u ≤ -1/y u) :
    y t^2 ≤ y s^2-2*(t-s) := by
  have hsq (u : ℝ) (hu : u ∈ Icc s t) :
      HasDerivAt (fun u => y u^2) (2*y u*v u) u := by
    simpa only [Pi.pow_def,Nat.reduceSub,pow_one,Nat.cast_ofNat] using (hd u hu).pow 2
  have hc : ContinuousOn (fun u => y u^2) (Icc s t) :=
    fun u hu => (hsq u hu).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun u => y u^2) (interior (Icc s t)) :=
    fun u hu => (hsq u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hb : ∀ u ∈ interior (Icc s t), deriv (fun u => y u^2) u ≤ -2 := by
    intro u hu
    have hui := interior_subset hu
    rw [(hsq u hui).deriv]
    have hpos := hy u hui
    have hh := mul_le_mul_of_nonneg_left (hv u hui) (by positivity : 0 ≤ 2*y u)
    have he : (2*y u)*(-1/y u)= -2 := by field_simp
    linarith [he]
  have hh := (convex_Icc s t).image_sub_le_mul_sub_of_deriv_le hc hdiff hb
    s (left_mem_Icc.mpr hst) t (right_mem_Icc.mpr hst) hst
  linarith

theorem polynomial_branch_strip_bound (S : ℝ → Finset ℂ) (r v : ℝ → ℂ)
    (s t : ℝ) (hst : s ≤ t)
    (hr : ∀ u ∈ Icc s t, HasDerivAt r (v u) u)
    (hroot : ∀ u ∈ Icc s t, r u ∈ S u)
    (hi : ∀ u ∈ Icc s t, 0<(r u).im)
    (hc : ∀ u ∈ Icc s t, conj (r u) ∈ S u)
    (hmax : ∀ u ∈ Icc s t, ∀ b ∈ S u, b.im ≤ (r u).im)
    (hvelocity : ∀ u ∈ Icc s t, v u=
      (rootPolynomial (S u)).derivative.derivative.eval (r u)/
        (rootPolynomial (S u)).derivative.eval (r u)) :
    (r t).im^2 ≤ (r s).im^2-2*(t-s) := by
  apply squared_height_barrier (fun u => (r u).im) (fun u => (v u).im) s t hst hi
  · intro u hu
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt u (hr u hu)
  · intro u hu
    rw [hvelocity u hu]
    exact uppermost_polynomial_ratio (S u) (r u) (hroot u hu) (hi u hu)
      (hc u hu) (hmax u hu)

theorem interior_root_counterexample :
    let p : ℂ[X] := X^4+C 5*X^2+C 4
    p.eval I=0 ∧ p.eval (-I)=0 ∧ p.eval (2*I)=0 ∧ p.eval (-2*I)=0 ∧
      p.derivative.eval I ≠ 0 ∧
      (p.derivative.derivative.eval I/p.derivative.eval I).im=1/3 := by
  dsimp
  norm_num [derivative_add,derivative_mul,derivative_pow,mul_pow,pow_succ,Complex.ext_iff,Complex.mul_re,Complex.mul_im,
    Complex.div_im,Complex.normSq_apply]

def upwardHeight (t : ℝ) : ℝ :=
  Real.sqrt ((5-12*t-Real.sqrt (9-80*t+96*t^2))/2)

theorem upwardHeight_hasDerivAt : HasDerivAt upwardHeight (1/3) 0 := by
  have hD : HasDerivAt (fun t : ℝ => 9-80*t+96*t^2) (-80) 0 := by
    have hd := (C 9-C 80*X+C 96*X^2 : ℝ[X]).hasDerivAt 0
    norm_num [derivative_add,derivative_sub,derivative_mul,derivative_pow] at hd
    exact hd
  have hsq := hD.sqrt (by norm_num)
  have hx := (((hasDerivAt_const (0:ℝ) 5).sub ((hasDerivAt_id 0).const_mul 12)).sub hsq).div_const 2
  have hx' : HasDerivAt (fun t : ℝ => (5-12*t-Real.sqrt (9-80*t+96*t^2))/2) (2/3) 0 := by
    norm_num [Pi.sub_def] at hx
    exact hx
  have hy := hx'.sqrt (by norm_num)
  change HasDerivAt upwardHeight _ 0 at hy
  norm_num at hy
  exact hy

def upwardPolynomial (t : ℝ) : ℂ[X] :=
  X^4+C ((5-12*t : ℝ):ℂ)*X^2+C ((4-10*t+12*t^2 : ℝ):ℂ)

theorem upwardPolynomial_root (t : ℝ) (hD : 0 ≤ 9-80*t+96*t^2)
    (hx : 0 ≤ (5-12*t-Real.sqrt (9-80*t+96*t^2))/2) :
    (upwardPolynomial t).eval (I*(upwardHeight t : ℂ))=0 := by
  have hs := Real.sq_sqrt hD
  have hy : upwardHeight t^2=(5-12*t-Real.sqrt (9-80*t+96*t^2))/2 := Real.sq_sqrt hx
  have he : upwardHeight t^4-(5-12*t)*upwardHeight t^2+4-10*t+12*t^2=0 := by
    rw [show upwardHeight t^4=(upwardHeight t^2)^2 by ring,hy]
    nlinarith [hs]
  have htwo : (I*(upwardHeight t : ℂ))^2= -((upwardHeight t^2 : ℝ):ℂ) := by
    rw [mul_pow,Complex.I_sq,← Complex.ofReal_pow]; ring
  have hfour : (I*(upwardHeight t : ℂ))^4=((upwardHeight t^4 : ℝ):ℂ) := by
    rw [show (I*(upwardHeight t : ℂ))^4=((I*(upwardHeight t : ℂ))^2)^2 by ring,
      htwo,neg_sq,← Complex.ofReal_pow]
    congr 1
    ring
  simp only [upwardPolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_C,htwo,hfour]
  have hec := congrArg (fun x : ℝ => (x : ℂ)) he
  push_cast at hec ⊢
  linear_combination hec

theorem upwardPolynomial_heat (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => (upwardPolynomial s).eval z)
      (-(upwardPolynomial t).derivative.derivative.eval z) t := by
  have hd := (C (z^4+5*z^2+4)-C (12*z^2+10)*X+C 12*X^2 : ℂ[X]).hasDerivAt (t:ℂ)
  have hr := hd.comp_ofReal
  convert hr using 1 <;>
    simp [upwardPolynomial,derivative_add,derivative_mul,derivative_pow] <;> ring

theorem upwardPolynomial_actual_branch :
    ∀ᶠ t : ℝ in 𝓝 0,
      (upwardPolynomial t).eval (I*(upwardHeight t : ℂ))=0 := by
  have hD : Continuous (fun t : ℝ => 9-80*t+96*t^2) := by fun_prop
  have hx : Continuous (fun t : ℝ => (5-12*t-Real.sqrt (9-80*t+96*t^2))/2) := by fun_prop
  have hpD := (hD.tendsto 0).eventually (Ioi_mem_nhds
    (by norm_num : (0:ℝ)<9-80*0+96*0^2))
  have hpx := (hx.tendsto 0).eventually (Ioi_mem_nhds
    (by norm_num : (0:ℝ)<(5-12*0-Real.sqrt (9-80*0+96*0^2))/2))
  filter_upwards [hpD,hpx] with t ht hx
  exact upwardPolynomial_root t (le_of_lt ht) (le_of_lt hx)

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticRootMotion
