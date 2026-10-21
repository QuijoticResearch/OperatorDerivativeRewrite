import Foundation.RiemannEvenEvolution
import Foundation.RiemannEvenRealSaddle
import Foundation.FactorialAnalyticDomain
import Foundation.FactorialAnalyticFunctions
import Mathlib.Topology.Order.Compact

/-! Actual Xi-flow derivatives do not belong to the factorial lp-one domain.
The real-function realization is excluded by a verified real/complex derivative bridge. -/
noncomputable section
open MeasureTheory Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannFactorialObstruction
open RiemannEvenDomain RiemannEvenFlow RiemannEvenEvolution
open RiemannQuarticFlow (halfLine)

theorem even_derivative_zero (m n : ℕ) (t : ℝ) :
    iteratedDeriv (2*n) (flow m t) 0 =
      (-1 : ℂ)^n*((∫ u : ℝ, weighted m (2*n) t 0 u ∂halfLine : ℝ) : ℂ) := by
  have hs : (-1 : ℂ)^(2*n)=1 := by rw [pow_mul]; norm_num
  rw [flow_iteratedDeriv]
  simp only [symmetricJet,neg_zero,hs,one_mul,add_self_div_two]
  have hp (u : ℝ) : (Complex.I*(u : ℂ))^(2*n) =
      (-1 : ℂ)^n*(u : ℂ)^(2*n) := by
    rw [mul_pow,pow_mul,Complex.I_sq]
  have hi (u : ℝ) : integrand m (2*n) t 0 u =
      (-1 : ℂ)^n*(weighted m (2*n) t 0 u : ℂ) := by
    simp only [integrand,mul_zero,Complex.exp_zero,mul_one,hp]
    unfold weighted
    simp only [pow_zero,one_mul]
    push_cast
    ring
  unfold jet
  simp_rw [hi]
  rw [integral_const_mul,integral_complex_ofReal]

theorem even_derivative_norm (m n : ℕ) (t : ℝ) :
    ‖iteratedDeriv (2*n) (flow m t) 0‖ =
      ∫ u : ℝ, weighted m (2*n) t 0 u ∂halfLine := by
  have hn : 0 ≤ ∫ u : ℝ, weighted m (2*n) t 0 u ∂halfLine := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact weighted_nonneg m (2*n) t 0 u hu
  rw [even_derivative_zero,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hn]

theorem positive_interval_lower (m : ℕ) (t : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ u ∈ Icc (2 : ℝ) 3, d ≤ weighted m 0 t 0 u := by
  have hsub : Icc (2 : ℝ) 3 ⊆ Ici (0 : ℝ) := by intro u hu; exact le_trans (by norm_num) hu.1
  obtain ⟨u,hu,hmin⟩ := (isCompact_Icc : IsCompact (Icc (2 : ℝ) 3)).exists_isMinOn
    (nonempty_Icc.mpr (by norm_num)) ((weighted_continuousOn m 0 t 0).mono hsub)
  exact ⟨weighted m 0 t 0 u,RiemannEvenRealSaddle.weighted_pos m t u (hsub hu),
    fun v hv => hmin hv⟩

theorem even_derivatives_exponential_lower (m : ℕ) (t : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℕ,
      d*(2 : ℝ)^(2*n) ≤ ‖iteratedDeriv (2*n) (flow m t) 0‖ := by
  obtain ⟨d,hd,hbase⟩ := positive_interval_lower m t
  refine ⟨d,hd,?_⟩
  intro n
  rw [even_derivative_norm]
  have hsub : Icc (2 : ℝ) 3 ⊆ Ici (0 : ℝ) := by intro u hu; exact le_trans (by norm_num) hu.1
  have hi : IntegrableOn (weighted m (2*n) t 0) (Ici (0 : ℝ)) := weighted_integrable m (2*n) t 0
  have hlocal := setIntegral_mono_on (integrableOn_const (by simp [Real.volume_Icc]))
    (hi.mono_set hsub) measurableSet_Icc (f := fun _ : ℝ => d*2^(2*n))
    (g := weighted m (2*n) t 0) (by
      intro u hu
      have he : weighted m (2*n) t 0 u = u^(2*n)*weighted m 0 t 0 u := by
        unfold weighted
        simp only [pow_zero,one_mul]
        ring
      rw [he]
      calc
        d*2^(2*n) = 2^(2*n)*d := by ring
        _ ≤ u^(2*n)*weighted m 0 t 0 u :=
          mul_le_mul (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hu.1 _)
            (hbase u hu) hd.le (pow_nonneg (hsub hu) _))
  have hwhole := setIntegral_mono_set hi
    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu;
        exact weighted_nonneg m (2*n) t 0 u hu)
    (Eventually.of_forall fun u hu => hsub hu)
  have hconst : (∫ _u : ℝ in Icc (2 : ℝ) 3, d*2^(2*n)) = d*2^(2*n) := by
    norm_num [MeasureTheory.integral_const,Measure.real,Real.volume_Icc]
  rw [hconst] at hlocal
  exact hlocal.trans hwhole

theorem not_summable_derivative_norms (m : ℕ) (t : ℝ) :
    ¬ Summable (fun n : ℕ => ‖iteratedDeriv n (flow m t) 0‖) := by
  intro hs
  obtain ⟨d,hd,hlower⟩ := even_derivatives_exponential_lower m t
  have hinj : Function.Injective (fun n : ℕ => 2*n) := by intro a b h; change 2*a=2*b at h; omega
  have ht := (hs.comp_injective hinj).tendsto_atTop_zero
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds (half_pos hd))).exists
  have hpow : (1 : ℝ) ≤ 2^(2*n) := one_le_pow₀ (by norm_num)
  have hbound := (le_mul_of_one_le_right hd.le hpow).trans (hlower n)
  change ‖iteratedDeriv (2*n) (flow m t) 0‖ < d/2 at hn
  linarith

theorem no_factorial_derivative_coefficients (m : ℕ) (t : ℝ) :
    ¬ ∃ u : FactorialAnalyticDomain.H, ∀ n : ℕ,
      iteratedDeriv n (flow m t) 0 = (u n : ℂ) := by
  rintro ⟨u,hu⟩
  apply not_summable_derivative_norms m t
  have hs := FactorialAnalyticDomain.sum_norm u
  simpa only [hu,Complex.norm_real,Real.norm_eq_abs] using hs

theorem real_iteratedDeriv (m n : ℕ) (t x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (flow m t (y : ℂ)).re) x =
      (symmetricJet m n t (x : ℂ)).re := by
  induction n generalizing x with
  | zero => simp only [iteratedDeriv_zero,symmetricJet_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ,show iteratedDeriv n (fun y : ℝ => (flow m t (y : ℂ)).re) =
      (fun y : ℝ => (symmetricJet m n t (y : ℂ)).re) from funext ih]
    exact (symmetricJet_hasDerivAt m n t (x : ℂ)).real_of_complex.deriv

theorem even_real_derivative_norm (m n : ℕ) (t : ℝ) :
    ‖iteratedDeriv (2*n) (fun y : ℝ => (flow m t (y : ℂ)).re) 0‖ =
      ‖iteratedDeriv (2*n) (flow m t) 0‖ := by
  rw [real_iteratedDeriv,← flow_iteratedDeriv]
  simp only [Complex.ofReal_zero]
  rw [even_derivative_zero]
  have he : (-1 : ℂ)^n*
      ((∫ u : ℝ, weighted m (2*n) t 0 u ∂halfLine : ℝ) : ℂ) =
      (((-1 : ℝ)^n*(∫ u : ℝ, weighted m (2*n) t 0 u ∂halfLine) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs]

theorem no_factorial_realization (m : ℕ) (t : ℝ) :
    ¬ ∃ u : FactorialAnalyticDomain.H, ∀ x : ℝ,
      FactorialAnalyticFunctions.realize u x = (flow m t (x : ℂ)).re := by
  rintro ⟨u,hu⟩
  have hf : (FactorialAnalyticFunctions.realize u : ℝ → ℝ) =
      (fun x : ℝ => (flow m t (x : ℂ)).re) := funext hu
  obtain ⟨d,hd,hlower⟩ := even_derivatives_exponential_lower m t
  have hinj : Function.Injective (fun n : ℕ => 2*n) := by
    intro a b h
    change 2*a=2*b at h
    omega
  have ht := ((FactorialAnalyticDomain.sum_norm u).comp_injective hinj).tendsto_atTop_zero
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds (half_pos hd))).exists
  have hc := FactorialAnalyticFunctions.coordinate_recovery u (2*n)
  rw [hf] at hc
  change ‖u (2*n)‖ < d/2 at hn
  rw [← hc,even_real_derivative_norm] at hn
  have hpow : (1 : ℝ) ≤ 2^(2*n) := one_le_pow₀ (by norm_num)
  have hb := (le_mul_of_one_le_right hd.le hpow).trans (hlower n)
  linarith

end OperatorDerivativeRewrite.Foundation.RiemannFactorialObstruction
