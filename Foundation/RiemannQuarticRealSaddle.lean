import Foundation.RiemannThetaHolomorphic
import Foundation.RiemannQuarticDomain
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.RealDeriv
/-! Actual real saddles of the quartically tilted arithmetic kernel.
Global maxima exist for every real time, and every global maximizer escapes
any fixed compact interval as t tends to infinity. Interior maxima solve
the exact complex local-phase equation at frequency zero. No uniqueness,
nondegeneracy, nonzero-frequency saddle continuation or contour bound follows. -/
noncomputable section
open Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticRealSaddle
open RiemannQuarticKernel RiemannQuarticDomain RiemannThetaComplexKernel

theorem weighted_tendsto_zero (t : ℝ) :
    Tendsto (weighted 0 t 0) atTop (nhds 0) :=
  (weighted_isBigO 0 t 0).trans_tendsto Real.tendsto_exp_neg_atTop_nhds_zero

theorem weighted_pos (t u : ℝ) (hu : 0 ≤ u) : 0 < weighted 0 t 0 u := by
  simpa only [weighted, pow_zero, one_mul, zero_mul, add_zero] using
    mul_pos (Real.exp_pos (t*u^4)) (kernel_pos u hu)

theorem exists_global_max (t : ℝ) :
    ∃ u ∈ Ici (0 : ℝ), IsMaxOn (weighted 0 t 0) (Ici 0) u := by
  have hp := weighted_pos t 0 le_rfl
  have he : ∀ᶠ u in atTop, weighted 0 t 0 u < weighted 0 t 0 0 :=
    (weighted_tendsto_zero t).eventually (gt_mem_nhds hp)
  obtain ⟨B,hB⟩ := eventually_atTop.1 he
  obtain ⟨u,hu,hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) (max B 0)).Nonempty from ⟨0,le_rfl,le_max_right _ _⟩)
    ((weighted_continuousOn 0 t 0).mono (fun x hx => hx.1))
  refine ⟨u,hu.1,?_⟩
  intro x hx
  by_cases hxu : x ≤ max B 0
  · exact hm ⟨hx,hxu⟩
  · have hBx : B ≤ x := (le_max_left B 0).trans (le_of_lt (lt_of_not_ge hxu))
    exact (hB x hBx).le.trans (hm ⟨le_rfl,le_max_right B 0⟩)

theorem kernel_hasDerivAt (u : ℝ) :
    HasDerivAt kernel (kernelDerivative (u : ℂ)).re u := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have hd := (kernelComplex_hasDerivAt (u : ℂ) he).real_of_complex
  convert hd using 1
  funext x
  rw [kernelComplex_real]
  simp

theorem weighted_hasDerivAt (t u : ℝ) :
    HasDerivAt (weighted 0 t 0)
      (Real.exp (t*u^4)*(4*t*u^3*kernel u+(kernelDerivative (u : ℂ)).re)) u := by
  have h := ((((hasDerivAt_id u).pow 4).const_mul t).exp).mul (kernel_hasDerivAt u)
  convert h using 1
  · funext x
    simp [weighted]
  · simp only [id_eq]
    norm_num
    ring

theorem maxima_escape (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted 0 t 0) (Ici 0) u → R < u := by
  obtain ⟨v,hv,hm⟩ := isCompact_Icc.exists_isMaxOn
    (show (Icc (0 : ℝ) R).Nonempty from ⟨0,le_rfl,hR⟩)
    (kernel_continuousOn.mono (fun x hx => hx.1))
  have hb : 0 < kernel (R+1) := kernel_pos _ (by linarith)
  have hgap : 0 < (R+1)^4-R^4 := by
    apply sub_pos.mpr
    exact pow_lt_pow_left₀ (by linarith : R < R+1) hR (by norm_num)
  have hlim : Tendsto (fun t : ℝ => Real.exp (t*((R+1)^4-R^4))) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_mul_const hgap)
  have he : ∀ᶠ t in atTop, kernel v/kernel (R+1) < Real.exp (t*((R+1)^4-R^4)) :=
    hlim.eventually (eventually_gt_atTop _)
  filter_upwards [he,eventually_ge_atTop (0 : ℝ)] with t ht ht0
  intro u hu hmax
  by_contra hnot
  have huR : u ≤ R := le_of_not_gt hnot
  have hbase : weighted 0 t 0 u ≤ Real.exp (t*R^4)*kernel v := by
    have hp : u^4 ≤ R^4 := pow_le_pow_left₀ hu huR 4
    have hk := hm (show u ∈ Icc (0 : ℝ) R from ⟨hu,huR⟩)
    simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
    apply mul_le_mul _ hk (kernel_pos u hu).le
      (Real.exp_pos _).le
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp ht0)
  have hratio : kernel v < Real.exp (t*((R+1)^4-R^4))*kernel (R+1) :=
    (div_lt_iff₀ hb).mp ht
  have hstrict : Real.exp (t*R^4)*kernel v < weighted 0 t 0 (R+1) := by
    calc
      _ < Real.exp (t*R^4)*(Real.exp (t*((R+1)^4-R^4))*kernel (R+1)) :=
        mul_lt_mul_of_pos_left hratio (Real.exp_pos _)
      _ = _ := by
        simp only [weighted,pow_zero,one_mul,zero_mul,add_zero]
        rw [← mul_assoc, ← Real.exp_add]
        congr 1
        congr 1
        ring
  exact (not_lt_of_ge (hmax (show R+1 ∈ Ici (0 : ℝ) from by change 0 ≤ R+1; linarith)))
    (hbase.trans_lt hstrict)

theorem max_real_stationary (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) :
    4*t*u^3+(kernelDerivative (u : ℂ)).re/kernel u=0 := by
  have hlocal := hm.isLocalMax (Ici_mem_nhds hu)
  have hz := hlocal.hasDerivAt_eq_zero (weighted_hasDerivAt t u)
  have hres : 4*t*u^3*kernel u+(kernelDerivative (u : ℂ)).re=0 :=
    (mul_eq_zero.mp hz).resolve_left (Real.exp_ne_zero _)
  have hk := ne_of_gt (kernel_pos u hu.le)
  field_simp
  simpa using hres

theorem eventually_exists_real_saddle (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t in atTop, ∃ u : ℝ, R < u ∧
      IsMaxOn (weighted 0 t 0) (Ici 0) u ∧
      4*t*u^3+(kernelDerivative (u : ℂ)).re/kernel u=0 := by
  filter_upwards [maxima_escape R hR] with t ht
  obtain ⟨u,hu,hm⟩ := exists_global_max t
  have hRu := ht u hu hm
  exact ⟨u,hRu,hm,max_real_stationary t u (lt_of_le_of_lt hR hRu) hm⟩

theorem kernelDerivative_real (u : ℝ) :
    kernelDerivative (u : ℂ)=
      ((30*Real.pi^2*Real.exp (9*u)*thetaMoment 4 (Real.exp (4*u))-
        8*Real.pi^3*Real.exp (13*u)*thetaMoment 6 (Real.exp (4*u))-
        15*Real.pi*Real.exp (5*u)*thetaMoment 2 (Real.exp (4*u)) : ℝ) : ℂ) := by
  have he (a : ℝ) : Complex.exp ((a : ℂ)*(u : ℂ))=(Real.exp (a*u) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp]
  unfold kernelDerivative
  rw [show (4 : ℂ)=((4 : ℝ) : ℂ) by norm_num, he 4]
  rw [moment_real 4 _ (Real.exp_pos _),moment_real 6 _ (Real.exp_pos _),
    moment_real 2 _ (Real.exp_pos _)]
  rw [show (9 : ℂ)=((9 : ℝ) : ℂ) by norm_num, he 9,
    show (13 : ℂ)=((13 : ℝ) : ℂ) by norm_num, he 13,
    show (5 : ℂ)=((5 : ℝ) : ℂ) by norm_num, he 5]
  push_cast
  rfl

theorem max_complex_stationary (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) :
    4*(t : ℂ)*(u : ℂ)^3+kernelDerivative (u : ℂ)/kernelComplex (u : ℂ)=0 := by
  have hs := max_real_stationary t u hu hm
  have him : (kernelDerivative (u : ℂ)).im=0 := by rw [kernelDerivative_real]; rfl
  have hcast : kernelDerivative (u : ℂ)=((kernelDerivative (u : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hcast,kernelComplex_real]
  exact_mod_cast hs

theorem eventually_exists_complex_saddle (R : ℝ) (hR : 0 ≤ R) :
    ∀ᶠ t in atTop, ∃ u : ℝ, R < u ∧
      IsMaxOn (weighted 0 t 0) (Ici 0) u ∧
      4*(t : ℂ)*(u : ℂ)^3+kernelDerivative (u : ℂ)/kernelComplex (u : ℂ)=0 := by
  filter_upwards [maxima_escape R hR] with t ht
  obtain ⟨u,hu,hm⟩ := exists_global_max t
  have hRu := ht u hu hm
  exact ⟨u,hRu,hm,max_complex_stationary t u (lt_of_le_of_lt hR hRu) hm⟩

theorem max_localPhase_hasDerivAt (t u : ℝ) (hu : 0 < u)
    (hm : IsMaxOn (weighted 0 t 0) (Ici 0) u) :
    HasDerivAt (localPhase t 0 (u : ℂ)) 0 (u : ℂ) := by
  have he : 0 < (Complex.exp (4*(u : ℂ))).re := by
    simpa only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      Complex.ofReal_re] using Real.exp_pos (4*u)
  have hn : kernelComplex (u : ℂ) ≠ 0 := by
    rw [kernelComplex_real]
    exact_mod_cast ne_of_gt (kernel_pos u hu.le)
  have h := localPhase_hasDerivAt t 0 (u : ℂ) he hn
  have hs := max_complex_stationary t u hu hm
  simpa only [Complex.ofReal_zero,mul_zero,add_zero,hs] using h
end OperatorDerivativeRewrite.Foundation.RiemannQuarticRealSaddle
