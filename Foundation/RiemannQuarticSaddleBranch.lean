import Foundation.RiemannQuarticSaddleTimes
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
/-! Actual analytic complex saddle branches near frequency zero.
A nonexceptional positive global maximum supplies an invertible exact phase
slope. The analytic inverse theorem constructs a branch and its derivative,
remaining locally in the theta convergence/nonvanishing domain. No uniform
frequency radius, global continuation or integrated contour bound is asserted. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleBranch
open RiemannQuarticKernel RiemannQuarticDomain RiemannThetaComplexKernel
open RiemannQuarticRealSaddle RiemannQuarticSaddleTimes

def complexSlope (t : ℝ) (w : ℂ) : ℂ :=
  4*(t : ℂ)*w^3+deriv kernelComplex w/kernelComplex w

theorem complexSlope_real (t u : ℝ) :
    complexSlope t (u : ℂ)=(phaseSlope t u : ℂ) := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have him : (kernelDerivative (u : ℂ)).im=0 := by rw [kernelDerivative_real]; rfl
  have hc : kernelDerivative (u : ℂ)=((kernelDerivative (u : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [complexSlope,(kernelComplex_hasDerivAt (u : ℂ) he).deriv,hc,kernelComplex_real]
  unfold phaseSlope
  rw [(kernel_hasDerivAt u).deriv]
  push_cast
  rfl

theorem complexSlope_analyticAt (t u : ℝ) (hu : 0 < u) :
    AnalyticAt ℂ (complexSlope t) (u : ℂ) := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have hk : kernelComplex (u : ℂ) ≠ 0 := by
    rw [kernelComplex_real]
    exact_mod_cast ne_of_gt (kernel_pos u hu.le)
  have ha := kernelComplex_analyticAt (u : ℂ) he
  exact (analyticAt_const.mul (analyticAt_id.pow 3)).add (ha.deriv.div ha hk)

theorem complexSlope_deriv_ne_zero (t u : ℝ) (ht : t ∉ exceptionalTimes) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) :
    deriv (complexSlope t) (u : ℂ) ≠ 0 := by
  have ha := complexSlope_analyticAt t u hu
  have hr : HasDerivAt (phaseSlope t) (deriv (complexSlope t) (u : ℂ)).re u := by
    convert ha.differentiableAt.hasDerivAt.real_of_complex using 1
    funext x
    rw [complexSlope_real]
    rfl
  intro hz
  have he := hr.deriv
  rw [hz,Complex.zero_re] at he
  exact nonexceptional_max_nondegenerate t u ht hu hm he

theorem complexSlope_zero_at_max (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) : complexSlope t (u : ℂ)=0 := by
  rw [complexSlope_real]
  have hs : phaseSlope t u=0 := by
    unfold phaseSlope
    rw [(kernel_hasDerivAt u).deriv]
    exact max_real_stationary t u hu hm
  rw [hs,Complex.ofReal_zero]

theorem exists_local_saddle_branch (t u : ℝ) (ht : t ∉ exceptionalTimes) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) :
    ∃ branch : ℂ → ℂ, branch 0=(u : ℂ) ∧ AnalyticAt ℂ branch 0 ∧
      HasStrictDerivAt branch (-Complex.I/deriv (complexSlope t) (u : ℂ)) 0 ∧
      ∀ᶠ z in nhds (0 : ℂ), complexSlope t (branch z)=-(Complex.I*z) ∧
        0 < (Complex.exp (4*branch z)).re ∧ kernelComplex (branch z) ≠ 0 := by
  have ha := complexSlope_analyticAt t u hu
  have hf := ha.hasStrictDerivAt
  have hn := complexSlope_deriv_ne_zero t u ht hu hm
  have hz := complexSlope_zero_at_max t u hu hm
  let inv := hf.localInverse (complexSlope t) (deriv (complexSlope t) (u : ℂ)) (u : ℂ) hn
  have hleft : inv (complexSlope t (u : ℂ))=(u : ℂ) :=
    (hf.eventually_left_inverse hn).self_of_nhds
  have hbase : inv 0=(u : ℂ) := by simpa only [hz] using hleft
  have hd : HasStrictDerivAt inv (deriv (complexSlope t) (u : ℂ))⁻¹ 0 := by
    simpa only [hz] using hf.to_localInverse hn
  have hright : ∀ᶠ y in nhds (0 : ℂ), complexSlope t (inv y)=y := by
    simpa only [hz] using hf.eventually_right_inverse hn
  have hab : AnalyticAt ℂ (fun z : ℂ => inv (-(Complex.I*z))) 0 := by
    have hainv : AnalyticAt ℂ inv (-(Complex.I*(0 : ℂ))) := by
      simpa only [hz,mul_zero,neg_zero] using ha.analyticAt_localInverse hn
    have hneg : AnalyticAt ℂ (fun z : ℂ => -(Complex.I*z)) 0 := by fun_prop
    exact AnalyticAt.comp (g := inv) (f := fun z : ℂ => -(Complex.I*z)) hainv hneg
  refine ⟨(fun z => inv (-(Complex.I*z))),?_,hab,?_,?_⟩
  · simpa using hbase
  · have hmul := (hasStrictDerivAt_id (0 : ℂ)).const_mul (-Complex.I)
    have hdf : HasStrictDerivAt inv (deriv (complexSlope t) (u : ℂ))⁻¹ (-Complex.I*(0 : ℂ)) := by
      simpa only [mul_zero] using hd
    have hcomp := hdf.comp 0 hmul
    convert hcomp using 1
    · funext z
      congr 1
      ring
    · simp only [div_eq_mul_inv]
      ring
  · have hc : Tendsto (fun z : ℂ => -(Complex.I*z)) (nhds 0) (nhds 0) := by
      have h : ContinuousAt (fun z : ℂ => -(Complex.I*z)) 0 := by fun_prop
      simpa only [ContinuousAt,mul_zero,neg_zero] using h
    have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
      simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
        Complex.ofReal_re] using Real.exp_pos (4*u)
    have hk : kernelComplex (u : ℂ) ≠ 0 := by
      rw [kernelComplex_real]
      exact_mod_cast ne_of_gt (kernel_pos u hu.le)
    have hd : ∀ᶠ w in nhds (u : ℂ), 0 < (Complex.exp (4*w)).re :=
      (show ContinuousAt (fun w : ℂ => (Complex.exp (4*w)).re) (u : ℂ) from by
        fun_prop).eventually (lt_mem_nhds he)
    have hkn := (kernelComplex_analyticAt (u : ℂ) he).continuousAt.eventually_ne hk
    have hb : Tendsto (fun z : ℂ => inv (-(Complex.I*z))) (nhds 0) (nhds (u : ℂ)) := by
      have h := hab.continuousAt
      simpa only [ContinuousAt,mul_zero,neg_zero,hbase] using h
    filter_upwards [hc.eventually hright,hb.eventually hd,hb.eventually hkn] with z hz hd hk
    exact ⟨hz,hd,hk⟩
end OperatorDerivativeRewrite.Foundation.RiemannQuarticSaddleBranch
