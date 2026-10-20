import Foundation.RiemannEvenRealSaddle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-! Actual complex saddle branches for integer-even tilts, together with
normalized local phases and reconstruction of the analytic amplitude.
All neighborhoods are local; no uniform radius or contour estimate is asserted. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannEvenSaddleBranch
open RiemannQuarticKernel RiemannEvenDomain RiemannThetaComplexKernel
open RiemannEvenRealSaddle

def complexSlope (m : ℕ) (t : ℝ) (w : ℂ) : ℂ :=
  ((2*m : ℕ) : ℂ)*(t : ℂ)*w^(2*m-1)+deriv kernelComplex w/kernelComplex w

theorem complexSlope_quartic (t : ℝ) :
    complexSlope 2 t = RiemannQuarticSaddleBranch.complexSlope t := rfl

theorem complexSlope_real (m : ℕ) (t u : ℝ) :
    complexSlope m t (u : ℂ) = (phaseSlope m t u : ℂ) := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat,← Complex.ofReal_mul,← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have him : (kernelDerivative (u : ℂ)).im = 0 := by
    rw [RiemannQuarticRealSaddle.kernelDerivative_real]
    rfl
  have hc : kernelDerivative (u : ℂ) = ((kernelDerivative (u : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [complexSlope,(kernelComplex_hasDerivAt (u : ℂ) he).deriv,hc,kernelComplex_real]
  unfold phaseSlope
  rw [(RiemannQuarticRealSaddle.kernel_hasDerivAt u).deriv]
  push_cast
  rfl

theorem complexSlope_analyticAt (m : ℕ) (t u : ℝ) (hu : 0 < u) :
    AnalyticAt ℂ (complexSlope m t) (u : ℂ) := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat,← Complex.ofReal_mul,← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have hk : kernelComplex (u : ℂ) ≠ 0 := by
    rw [kernelComplex_real]
    exact_mod_cast ne_of_gt (kernel_pos u hu.le)
  have ha := kernelComplex_analyticAt (u : ℂ) he
  exact (analyticAt_const.mul (analyticAt_id.pow (2*m-1))).add (ha.deriv.div ha hk)

theorem complexSlope_deriv_ne_zero_of_real (m : ℕ) (t u : ℝ) (hu : 0 < u)
    (hreal : deriv (phaseSlope m t) u ≠ 0) : deriv (complexSlope m t) (u : ℂ) ≠ 0 := by
  have ha := complexSlope_analyticAt m t u hu
  have hr : HasDerivAt (phaseSlope m t) (deriv (complexSlope m t) (u : ℂ)).re u := by
    convert ha.differentiableAt.hasDerivAt.real_of_complex using 1
    funext x
    rw [complexSlope_real]
    rfl
  intro hz
  have he := hr.deriv
  rw [hz,Complex.zero_re] at he
  exact hreal he

theorem complexSlope_zero_at_max (m : ℕ) (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted m 0 t 0) (Ici 0) u) : complexSlope m t (u : ℂ) = 0 := by
  rw [complexSlope_real,max_real_stationary m t u hu hm,Complex.ofReal_zero]

def localPhase (m : ℕ) (t : ℝ) (z base w : ℂ) : ℂ :=
  (t : ℂ)*w^(2*m)+Complex.I*z*w+Complex.log (kernelComplex w/kernelComplex base)

theorem localPhase_quartic (t x : ℝ) (base : ℂ) :
    localPhase 2 t (x : ℂ) base = RiemannThetaComplexKernel.localPhase t x base := rfl

theorem localPhase_analyticAt (m : ℕ) (t : ℝ) (z u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    AnalyticAt ℂ (localPhase m t z u) u := by
  exact ((analyticAt_const.mul (analyticAt_id.pow (2*m))).add
    (analyticAt_const.mul analyticAt_id)).add (kernel_normalized_log_analyticAt u hu hne)

theorem localPhase_hasDerivAt (m : ℕ) (t : ℝ) (z u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    HasDerivAt (localPhase m t z u) (complexSlope m t u+Complex.I*z) u := by
  have h := ((((hasDerivAt_id u).pow (2*m)).const_mul (t : ℂ)).add
    ((hasDerivAt_id u).const_mul (Complex.I*z))).add
    (kernel_normalized_log_hasDerivAt u hu hne)
  rw [complexSlope,(kernelComplex_hasDerivAt u hu).deriv]
  convert h using 1
  · funext w; rfl
  · simp only [id_eq]
    ring

theorem localPhase_reconstruct (m : ℕ) (t : ℝ) (z u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0) :
    ∀ᶠ w in nhds u, kernelComplex u*Complex.exp (localPhase m t z u w) =
      Complex.exp ((t : ℂ)*w^(2*m)+Complex.I*z*w)*kernelComplex w := by
  filter_upwards [kernel_normalized_log_reconstruct u hu hne] with w hw
  rw [localPhase,Complex.exp_add]
  calc
    _ = Complex.exp ((t : ℂ)*w^(2*m)+Complex.I*z*w)*
        (kernelComplex u*Complex.exp (Complex.log (kernelComplex w/kernelComplex u))) := by ring
    _ = _ := by rw [hw]

theorem localPhase_reconstruct_real_integrand (m : ℕ) (t u : ℝ) (z : ℂ) (hu : 0 ≤ u) :
    ∀ᶠ v : ℝ in nhds u,
      kernelComplex (u : ℂ)*Complex.exp (localPhase m t z (u : ℂ) (v : ℂ)) =
        RiemannEvenFlow.integrand m 0 t z v := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat,← Complex.ofReal_mul,← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have hk : kernelComplex (u : ℂ) ≠ 0 := by
    rw [kernelComplex_real]
    exact_mod_cast ne_of_gt (kernel_pos u hu)
  have hc : Tendsto (fun v : ℝ => (v : ℂ)) (nhds u) (nhds (u : ℂ)) :=
    Complex.continuous_ofReal.continuousAt
  filter_upwards [hc.eventually (localPhase_reconstruct m t z (u : ℂ) he hk)] with v hv
  rw [hv,kernelComplex_real,Complex.exp_add]
  have hcast : (t : ℂ)*(v : ℂ)^(2*m) = ((t*v^(2*m) : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast,← Complex.ofReal_exp]
  simp only [RiemannEvenFlow.integrand,weighted,pow_zero,one_mul,mul_one,zero_mul,add_zero,
    Complex.ofReal_mul,Complex.ofReal_exp]
  rw [show Complex.I*z*(v : ℂ) = Complex.I*(v : ℂ)*z by ring]
  ring

theorem localPhase_stationary (m : ℕ) (t : ℝ) (z u : ℂ)
    (hu : 0 < (Complex.exp (4*u)).re) (hne : kernelComplex u ≠ 0)
    (hs : complexSlope m t u = -(Complex.I*z)) :
    HasDerivAt (localPhase m t z u) 0 u := by
  simpa only [hs,neg_add_cancel] using localPhase_hasDerivAt m t z u hu hne

theorem exists_local_saddle_branch_of_deriv_ne_zero (m : ℕ) (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted m 0 t 0) (Ici 0) u)
    (hn : deriv (complexSlope m t) (u : ℂ) ≠ 0) :
    ∃ branch : ℂ → ℂ, branch 0=(u : ℂ) ∧ AnalyticAt ℂ branch 0 ∧
      HasStrictDerivAt branch (-Complex.I/deriv (complexSlope m t) (u : ℂ)) 0 ∧
      ∀ᶠ z in nhds (0 : ℂ), complexSlope m t (branch z)=-(Complex.I*z) ∧
        0 < (Complex.exp (4*branch z)).re ∧ kernelComplex (branch z) ≠ 0 := by
  have ha := complexSlope_analyticAt m t u hu
  have hf := ha.hasStrictDerivAt
  have hz := complexSlope_zero_at_max m t u hu hm
  let inv := hf.localInverse (complexSlope m t) (deriv (complexSlope m t) (u : ℂ)) (u : ℂ) hn
  have hleft : inv (complexSlope m t (u : ℂ))=(u : ℂ) :=
    (hf.eventually_left_inverse hn).self_of_nhds
  have hbase : inv 0=(u : ℂ) := by simpa only [hz] using hleft
  have hd : HasStrictDerivAt inv (deriv (complexSlope m t) (u : ℂ))⁻¹ 0 := by
    simpa only [hz] using hf.to_localInverse hn
  have hright : ∀ᶠ y in nhds (0 : ℂ), complexSlope m t (inv y)=y := by
    simpa only [hz] using hf.eventually_right_inverse hn
  have hab : AnalyticAt ℂ (fun z : ℂ => inv (-(Complex.I*z))) 0 := by
    have hainv : AnalyticAt ℂ inv (-(Complex.I*(0 : ℂ))) := by
      simpa only [hz,mul_zero,neg_zero] using ha.analyticAt_localInverse hn
    have hneg : AnalyticAt ℂ (fun z : ℂ => -(Complex.I*z)) 0 := by fun_prop
    exact AnalyticAt.comp (g := inv) (f := fun z : ℂ => -(Complex.I*z)) hainv hneg
  refine ⟨(fun z => inv (-(Complex.I*z))),?_,hab,?_,?_⟩
  · simpa using hbase
  · have hmul := (hasStrictDerivAt_id (0 : ℂ)).const_mul (-Complex.I)
    have hdf : HasStrictDerivAt inv (deriv (complexSlope m t) (u : ℂ))⁻¹ (-Complex.I*(0 : ℂ)) := by
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

theorem eventually_all_maxima_local_branches (m : ℕ) (hm : 0 < m) :
    ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted m 0 t 0) (Ici 0) u →
      ∃ branch : ℂ → ℂ, branch 0 = (u : ℂ) ∧ AnalyticAt ℂ branch 0 ∧
        HasStrictDerivAt branch (-Complex.I/deriv (complexSlope m t) (u : ℂ)) 0 ∧
        ∀ᶠ z in nhds (0 : ℂ), complexSlope m t (branch z) = -(Complex.I*z) ∧
          0 < (Complex.exp (4*branch z)).re ∧ kernelComplex (branch z) ≠ 0 ∧
          HasDerivAt (localPhase m t z (branch z)) 0 (branch z) := by
  filter_upwards [maxima_escape m hm 0 le_rfl,eventually_all_maxima_nondegenerate m hm] with t he hn
  intro u hu hmax
  have hu0 := he u hu hmax
  have hreal := (hn u hu hmax).2.ne
  have hc := complexSlope_deriv_ne_zero_of_real m t u hu0 hreal
  obtain ⟨branch,hbase,ha,hd,hbranch⟩ := exists_local_saddle_branch_of_deriv_ne_zero m t u hu0 hmax hc
  refine ⟨branch,hbase,ha,hd,?_⟩
  filter_upwards [hbranch] with z hz
  exact ⟨hz.1,hz.2.1,hz.2.2,localPhase_stationary m t z (branch z) hz.2.1 hz.2.2 hz.1⟩

theorem eventually_exists_local_saddle_branch (m : ℕ) (hm : 0 < m) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t : ℝ in atTop, ∃ u : ℝ, R < u ∧ IsMaxOn (weighted m 0 t 0) (Ici 0) u ∧
      ∃ branch : ℂ → ℂ, branch 0 = (u : ℂ) ∧ AnalyticAt ℂ branch 0 ∧
        HasStrictDerivAt branch (-Complex.I/deriv (complexSlope m t) (u : ℂ)) 0 ∧
        ∀ᶠ z in nhds (0 : ℂ), complexSlope m t (branch z) = -(Complex.I*z) ∧
          0 < (Complex.exp (4*branch z)).re ∧ kernelComplex (branch z) ≠ 0 ∧
          HasDerivAt (localPhase m t z (branch z)) 0 (branch z) := by
  filter_upwards [maxima_escape m hm R hR,eventually_all_maxima_local_branches m hm] with t he hb
  obtain ⟨u,hu,hmax⟩ := exists_global_max m t
  exact ⟨u,he u hu hmax,hmax,hb u hu hmax⟩

end OperatorDerivativeRewrite.Foundation.RiemannEvenSaddleBranch
