import Foundation.FactorialAnalyticFunctions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Foundation.L1BoundedSynthesis
import Foundation.SignedClockLaplaceObstruction
/-! Order-two analytic-functional clock and actual signed polynomial heat composition.
The domain is the existing l1 factorial derivative space, not a clock measure. -/
noncomputable section
open Polynomial MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.AnalyticInverseClock
open FactorialAnalyticDomain FactorialAnalyticHeat FactorialAnalyticFunctions

def evenAtom (n : ℕ) : H := lp.single 1 (2*n) (1:ℝ)

theorem evenAtom_norm (n : ℕ) : ‖evenAtom n‖≤1 := by
  rw [evenAtom,lp.norm_single (by norm_num : (0:ℝ≥0∞)<1)]
  norm_num

def evenLift : H →L[ℝ] H := L1BoundedSynthesis.synthesis evenAtom evenAtom_norm

theorem evenLift_norm : ‖evenLift‖≤1 := L1BoundedSynthesis.synthesis_norm _ _

def clock (t : ℝ) : H →L[ℝ] ℝ := (mean 1 t).comp evenLift

theorem clock_norm (t : ℝ) : ‖clock t‖≤Real.exp |t| := by
  calc
    _ ≤ ‖mean 1 t‖*‖evenLift‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.exp |t| *1 := mul_le_mul (mean_norm 1 t) evenLift_norm (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := mul_one _

theorem mean_single (t : ℝ) (n : ℕ) :
    mean 1 t (lp.single 1 n (1:ℝ))=t^n/(n.factorial:ℝ) := by
  have hn : (n.factorial:ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero n
  have he : polynomial (monomial n ((n.factorial:ℝ)⁻¹))=lp.single 1 n (1:ℝ) := by
    rw [polynomial_monomial,mul_inv_cancel₀ hn]
  rw [←he,mean_polynomial 1 (by norm_num),expectation_one_order]
  simp [eval_monomial,div_eq_mul_inv,mul_comm]

theorem clock_single (t : ℝ) (n : ℕ) (c : ℝ) :
    clock t (lp.single 1 n c)=c*t^(2*n)/((2*n).factorial:ℝ) := by
  change mean 1 t (evenLift (lp.single 1 n c))=_
  rw [evenLift,L1BoundedSynthesis.synthesis_single,map_smul]
  change c*mean 1 t (evenAtom n)=_
  rw [evenAtom,mean_single]
  ring

theorem clock_series (t : ℝ) (u : H) :
    HasSum (fun n : ℕ => u n*t^(2*n)/((2*n).factorial:ℝ)) (clock t u) := by
  have hs := (mean 1 t).hasSum
    (L1BoundedSynthesis.terms_summable evenAtom evenAtom_norm u).hasSum
  convert hs using 1
  · funext n
    rw [map_smul]
    change _=u n*mean 1 t (evenAtom n)
    rw [evenAtom,mean_single]
    ring
  · rfl

theorem clock_derivative_series (t : ℝ) (u : H) :
    HasSum (fun n : ℕ => iteratedDeriv n (realize u : ℝ → ℝ) 0*t^(2*n)/((2*n).factorial:ℝ))
      (clock t u) := by
  simpa only [coordinate_recovery] using clock_series t u

theorem clock_monomial (t c : ℝ) (n : ℕ) :
    clock t (polynomial (monomial n c))=(n.factorial:ℝ)*c*t^(2*n)/((2*n).factorial:ℝ) := by
  rw [polynomial_monomial,clock_single]

theorem clock_X_pow (t : ℝ) (n : ℕ) :
    clock t (polynomial (X^n))=(n.factorial:ℝ)*t^(2*n)/((2*n).factorial:ℝ) := by
  simpa only [← C_mul_X_pow_eq_monomial,map_one,one_mul,mul_one] using clock_monomial t 1 n

theorem clock_convergence (t : ℝ) {ι : Type*} {l : Filter ι} {f : ι → H} {u : H}
    (hf : Tendsto f l (𝓝 u)) : Tendsto (fun i => clock t (f i)) l (𝓝 (clock t u)) :=
  ((clock t).continuous.tendsto u).comp hf

theorem negative_square (t : ℝ) :
    clock t (polynomial ((X-C (t^2/2))^2))= -t^4/6 := by
  have he' (a : ℝ) : ((X-C a)^2 : Polynomial ℝ)=X^2-(2*a) • X+(a^2) • 1 := by
    simp only [smul_eq_C_mul,map_mul,map_pow,map_ofNat,mul_one]
    ring
  have he : ((X-C (t^2/2))^2 : Polynomial ℝ)=X^2-(t^2) • X+(t^4/4) • 1 := by
    have h1 : 2*(t^2/2)=t^2 := by ring
    have h2 : (t^2/2)^2=t^4/4 := by ring
    exact (he' (t^2/2)).trans (by rw [h1,h2])
  change clock t (polynomialMap ((X-C (t^2/2))^2))=_
  rw [he,map_add,map_sub,map_smul,map_smul,map_add,map_sub,map_smul,map_smul]
  change clock t (polynomial (X^2))-t^2*clock t (polynomial X)+t^4/4*clock t (polynomial 1)=_
  have h0 := clock_X_pow t 0
  have h1 := clock_X_pow t 1
  have h2 := clock_X_pow t 2
  norm_num at h0 h1 h2
  rw [h0,h1,h2]
  ring
theorem not_positive (t : ℝ) (ht : 0<t) :
    ¬∀ u : H, (∀ s : ℝ, 0≤realize u s) → 0≤clock t u := by
  intro h
  have hh := h (polynomial ((X-C (t^2/2))^2)) (fun s => by
    rw [realize_polynomial]
    simp only [eval_pow,eval_sub,eval_X,eval_C]
    positivity)
  rw [negative_square] at hh
  have hp := pow_pos ht 4
  linarith

def exponentialJet (q : ℝ) (hq : |q|<1) : H := ⟨fun n => (-q)^n,by
  apply memℓp_gen
  have hs : Summable (fun n : ℕ => |q|^n) := summable_geometric_of_lt_one (abs_nonneg q) hq
  simpa only [ENNReal.toReal_one,Real.rpow_one,norm_pow,norm_neg,Real.norm_eq_abs] using hs⟩

theorem exponentialJet_apply (q : ℝ) (hq : |q|<1) (n : ℕ) :
    exponentialJet q hq n=(-q)^n := rfl

theorem exponentialJet_realize (q : ℝ) (hq : |q|<1) (s : ℝ) :
    realize (exponentialJet q hq) s=Real.exp (-q*s) := by
  have hs := series_coordinate 1 s (exponentialJet q hq) 0
  have he : HasSum (fun n : ℕ => (s^n/(n.factorial:ℝ))*(-q)^n) (Real.exp (-q*s)) := by
    have hx := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (-q*s)
    convert hx using 1
    · funext n
      simp only [smul_eq_mul,mul_pow,div_eq_mul_inv]
      ring
    · exact congrArg (fun f : ℝ → ℝ => f (-q*s)) Real.exp_eq_exp_ℝ
  change evolution 1 s (exponentialJet q hq) 0=_
  apply hs.unique
  simpa only [zero_add,one_mul,exponentialJet_apply] using he

theorem exponential_domain (q : ℝ) :
    (∃ u : H, ∀ s : ℝ, realize u s=Real.exp (-q*s)) ↔ |q|<1 := by
  constructor
  · rintro ⟨u,hu⟩
    have hf : (realize u : ℝ → ℝ)=(fun s : ℝ => Real.exp ((-q)*s)) := funext hu
    have hj (n : ℕ) : u n=(-q)^n := by
      rw [←coordinate_recovery u n,hf,iteratedDeriv_exp_const_mul]
      simp
    have hs := sum_norm u
    simp only [hj,norm_pow,norm_neg,Real.norm_eq_abs] at hs
    have hh := summable_geometric_iff_norm_lt_one.mp hs
    simpa only [Real.norm_eq_abs,abs_abs] using hh
  · intro hq
    exact ⟨exponentialJet q hq,exponentialJet_realize q hq⟩

theorem clock_exponential (t q : ℝ) (hq : |q|<1) (hq0 : 0≤q) :
    clock t (exponentialJet q hq)=SignedClockLaplaceObstruction.inverseTwo t q := by
  apply (clock_series t (exponentialJet q hq)).unique
  have hi := SignedClockLaplaceObstruction.inverseTwo_hasSum t q hq0
  rw [←SignedClockLaplaceObstruction.inverseTwo_eq_cos t q hq0] at hi
  convert hi using 1
  funext n
  rw [Real.Gamma_nat_eq_factorial,exponentialJet_apply,mul_pow,pow_mul]

theorem heat_coeff_bound (p : ℕ) (c : ℝ) (hc : |c|≤1) (u : H) (n : ℕ) :
    ‖c^n*u (p*n)‖≤‖u (p*n)‖ := by
  rw [norm_mul,norm_pow]
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact pow_le_one₀ (norm_nonneg c) (by simpa only [Real.norm_eq_abs] using hc)

def heatJetLinear (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) : H →ₗ[ℝ] H where
  toFun u := ⟨fun n => c^n*u (p*n),by
    apply memℓp_gen
    have hs := (sum_norm u).comp_injective (fun i j h => Nat.eq_of_mul_eq_mul_left hp h)
    have hi := hs.of_nonneg_of_le (fun n => norm_nonneg (c^n*u (p*n))) (heat_coeff_bound p c hc u)
    simpa only [ENNReal.toReal_one,Real.rpow_one] using hi⟩
  map_add' u v := by
    ext n
    change c^n*(u (p*n)+v (p*n))=c^n*u (p*n)+c^n*v (p*n)
    ring
  map_smul' a u := by
    ext n
    change c^n*(a*u (p*n))=a*(c^n*u (p*n))
    ring

theorem heatJetLinear_apply (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (u : H) (n : ℕ) :
    heatJetLinear p hp c hc u n=c^n*u (p*n) := rfl

theorem heatJetLinear_norm (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (u : H) :
    ‖heatJetLinear p hp c hc u‖≤‖u‖ := by
  have hinj : Function.Injective (fun n : ℕ => p*n) := fun i j h => Nat.eq_of_mul_eq_mul_left hp h
  have hs := (sum_norm u).comp_injective hinj
  rw [norm_eq_sum,norm_eq_sum]
  apply ((sum_norm (heatJetLinear p hp c hc u)).tsum_le_tsum (heat_coeff_bound p c hc u) hs).trans
  exact tsum_comp_le_tsum_of_inj (sum_norm u) (fun n => norm_nonneg (u n)) hinj

def heatJet (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) : H →L[ℝ] H :=
  (heatJetLinear p hp c hc).mkContinuous 1 (by simpa only [one_mul] using heatJetLinear_norm p hp c hc)

theorem heatJet_apply (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (u : H) (n : ℕ) :
    heatJet p hp c hc u n=c^n*u (p*n) := rfl

theorem heatJet_norm (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) : ‖heatJet p hp c hc‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun u => by
    change ‖heatJetLinear p hp c hc u‖≤1*‖u‖
    simpa only [one_mul] using heatJetLinear_norm p hp c hc u)

theorem heatJet_realize (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (u : H) (s : ℝ) :
    realize (heatJet p hp c hc u) s=mean p (c*s) u := by
  have hs := series_coordinate 1 s (heatJet p hp c hc u) 0
  have ht := series_coordinate p (c*s) u 0
  change evolution 1 s (heatJet p hp c hc u) 0=evolution p (c*s) u 0
  apply hs.unique
  convert ht using 1
  funext n
  simp only [zero_add,one_mul,heatJet_apply,mul_pow]
  ring

def composed (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (t : ℝ) : H →L[ℝ] ℝ :=
  (clock t).comp (heatJet p hp c hc)

theorem composed_norm (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (t : ℝ) :
    ‖composed p hp c hc t‖≤Real.exp |t| := by
  calc
    _ ≤ ‖clock t‖*‖heatJet p hp c hc‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ Real.exp |t| *1 := mul_le_mul (clock_norm t) (heatJet_norm p hp c hc) (norm_nonneg _) (Real.exp_pos _).le
    _ = _ := mul_one _

theorem composed_series (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (t : ℝ) (u : H) :
    HasSum (fun n : ℕ => c^n*u (p*n)*t^(2*n)/((2*n).factorial:ℝ)) (composed p hp c hc t u) := by
  exact clock_series t (heatJet p hp c hc u)

theorem heatJet_actual_kernel (m : ℕ) (hm : 0<m) (P : Polynomial ℝ)
    (s : ℝ≥0) (hs : 0<s) :
    realize (heatJet (2*m) (by omega) ((-1:ℝ)^(m+1)) (by simp) (polynomial P)) s=
      HigherHeatPolynomialRealization.kernelExpectation m hm s hs P := by
  rw [heatJet_realize]
  exact actual_mean m hm s hs P

theorem composed_convergence (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (t : ℝ)
    {ι : Type*} {l : Filter ι} {f : ι → H} {u : H} (hf : Tendsto f l (𝓝 u)) :
    Tendsto (fun i => composed p hp c hc t (f i)) l (𝓝 (composed p hp c hc t u)) :=
  ((composed p hp c hc t).continuous.tendsto u).comp hf

theorem composed_unique (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (t : ℝ)
    (L : H →L[ℝ] ℝ) (hL : ∀ P : Polynomial ℝ, L (polynomial P)=composed p hp c hc t (polynomial P)) :
    L=composed p hp c hc t := by
  apply ContinuousLinearMap.coeFn_injective
  apply polynomial_dense.equalizer L.continuous (composed p hp c hc t).continuous
  exact funext hL

theorem composed_difference (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1)
    (t T : ℝ) (ht : |t|≤T) (u v : H) :
    ‖composed p hp c hc t u-composed p hp c hc t v‖≤Real.exp T*‖u-v‖ := by
  have hb := (composed p hp c hc t).le_of_opNorm_le (composed_norm p hp c hc t) (u-v)
  rw [map_sub] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht) (norm_nonneg _))

theorem composed_uniform_convergence (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (T : ℝ)
    {ι : Type*} {l : Filter ι} {f : ι → H} {u : H} (hf : Tendsto f l (𝓝 u)) :
    TendstoUniformlyOn (fun i t => composed p hp c hc t (f i)) (fun t => composed p hp c hc t u)
      l {t : ℝ | |t|≤T} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have he : Tendsto (fun i => Real.exp T*‖f i-u‖) l (𝓝 0) := by
    simpa only [sub_self,norm_zero,mul_zero] using ((hf.sub (tendsto_const_nhds : Tendsto (fun _ : ι => u) l (𝓝 u))).norm.const_mul (Real.exp T))
  filter_upwards [he.eventually (gt_mem_nhds hε)] with i hi
  intro t ht
  rw [dist_eq_norm]
  exact (composed_difference p hp c hc t T ht u (f i)).trans_lt (by simpa only [norm_sub_rev] using hi)

theorem evenLift_even (u : H) (n : ℕ) : evenLift u (2*n)=u n := by
  let L := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 (2*n)
  have he := L.map_tsum (L1BoundedSynthesis.terms_summable evenAtom evenAtom_norm u)
  change L (evenLift u)=u n
  rw [evenLift,L1BoundedSynthesis.synthesis_apply,he,tsum_eq_single n]
  · change (u n • evenAtom n) (2*n)=u n
    simp [evenAtom]
  · intro j hj
    change (u j • evenAtom j) (2*n)=0
    have hne : 2*n≠2*j := by omega
    simp [evenAtom,lp.single_apply,hne]

theorem evenLift_odd (u : H) (n : ℕ) : evenLift u (2*n+1)=0 := by
  let L := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 1 (2*n+1)
  have he := L.map_tsum (L1BoundedSynthesis.terms_summable evenAtom evenAtom_norm u)
  change L (evenLift u)=0
  rw [evenLift,L1BoundedSynthesis.synthesis_apply,he]
  calc
    _ = ∑' _j : ℕ, (0:ℝ) := by
      apply tsum_congr
      intro j
      change (u j • evenAtom j) (2*n+1)=0
      have hne : 2*n+1≠2*j := by omega
      simp [evenAtom,lp.single_apply,hne]
    _ = 0 := tsum_zero

theorem evenLift_shift (u : H) : (shift^2) (evenLift u)=evenLift (shift u) := by
  ext k
  rcases k.even_or_odd' with ⟨n,rfl | rfl⟩
  · rw [shift_pow_apply,show 2*n+2=2*(n+1) from by omega,
      evenLift_even,evenLift_even,shift_apply]
  · rw [shift_pow_apply,show 2*n+1+2=2*(n+1)+1 from by omega,
      evenLift_odd,evenLift_odd]

theorem clock_zero (u : H) : clock 0 u=u 0 := by
  change realize (evenLift u) 0=u 0
  rw [realize_zero,show (0:ℕ)=2*0 from rfl,evenLift_even]

theorem clock_initial_velocity (u : H) : deriv (fun t : ℝ => clock t u) 0=0 := by
  change deriv (realize (evenLift u) : ℝ → ℝ) 0=0
  rw [realize_deriv,realize_zero,shift_apply,show (0:ℕ)+1=2*0+1 from rfl,evenLift_odd]

theorem clock_second_derivative (u : H) (a : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => clock t u) a=clock a (shift u) := by
  change iteratedDeriv 2 (realize (evenLift u) : ℝ → ℝ) a=_
  rw [realize_iterated,evenLift_shift]
  rfl

theorem heatJet_shift (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (u : H) :
    shift (heatJet p hp c hc u)=heatJet p hp c hc (c • (shift^p) u) := by
  ext n
  change c^(n+1)*u (p*(n+1))=c^n*(c*((shift^p) u) (p*n))
  rw [shift_pow_apply,pow_succ,Nat.mul_add,Nat.mul_one]
  ring

theorem composed_second_derivative (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1)
    (u : H) (a : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => composed p hp c hc t u) a=
      composed p hp c hc a (c • (shift^p) u) := by
  change iteratedDeriv 2 (fun t : ℝ => clock t (heatJet p hp c hc u)) a=_
  rw [clock_second_derivative,heatJet_shift]
  rfl

theorem clock_smooth (u : H) (n : ℕ) : ContDiff ℝ n (fun t : ℝ => clock t u) :=
  realize_smooth (evenLift u) n

theorem composed_smooth (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (u : H) (n : ℕ) :
    ContDiff ℝ n (fun t : ℝ => composed p hp c hc t u) :=
  clock_smooth (heatJet p hp c hc u) n

theorem composed_initial (p : ℕ) (hp : 0<p) (c : ℝ) (hc : |c|≤1) (u : H) :
    composed p hp c hc 0 u=u 0 ∧ deriv (fun t : ℝ => composed p hp c hc t u) 0=0 := by
  constructor
  · change clock 0 (heatJet p hp c hc u)=u 0
    rw [clock_zero,heatJet_apply]
    simp
  · exact clock_initial_velocity (heatJet p hp c hc u)

end OperatorDerivativeRewrite.Foundation.AnalyticInverseClock
