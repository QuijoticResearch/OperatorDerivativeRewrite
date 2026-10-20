import Foundation.RiemannRealOrderBranchObstruction
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Topology.Algebra.Polynomial

/-! Genuine real-axis Fourier decay for the actual real-order arithmetic
integrals and every Fourier jet. The result has no asymptotic rate and
does not assert any zero-location conclusion. -/
noncomputable section
open MeasureTheory Filter Set Metric Complex Polynomial
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourierDecay
open RiemannRealOrderFlow
open RiemannQuarticFlow (halfLine)

private theorem half_line_decay (f : ℝ → ℂ) :
    Tendsto (fun x : ℝ => ∫ u : ℝ, Complex.exp (I*(u : ℂ)*(x : ℂ))*f u ∂halfLine)
      (cocompact ℝ) (𝓝 0) := by
  let g := (Ici (0 : ℝ)).indicator f
  have hp : 0 < 2*Real.pi := by positivity
  have hnorm : Tendsto (fun x : ℝ => |x|) (cocompact ℝ) atTop := by
    simpa [Real.dist_eq] using tendsto_dist_right_cocompact_atTop (0 : ℝ)
  have hmag : Tendsto (fun x : ℝ => dist (-x/(2*Real.pi)) 0) (cocompact ℝ) atTop := by
    simpa only [Real.dist_eq,sub_zero,abs_div,abs_neg,abs_of_pos hp] using hnorm.atTop_div_const hp
  have hscale := tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ) hmag
  have hrl := (Real.tendsto_integral_exp_smul_cocompact g).comp hscale
  have he (x : ℝ) :
      (∫ u : ℝ, Real.fourierChar (-(u*(-x/(2*Real.pi)))) • g u) =
        ∫ u : ℝ, Complex.exp (I*(u : ℂ)*(x : ℂ))*f u ∂halfLine := by
    calc
      _ = ∫ u : ℝ, (Ici (0 : ℝ)).indicator
          (fun u => Complex.exp (I*(u : ℂ)*(x : ℂ))*f u) u := by
        apply integral_congr_ae
        filter_upwards [] with u
        dsimp [g]
        by_cases hu : u ∈ Ici (0 : ℝ)
        · rw [indicator_of_mem hu,indicator_of_mem hu,Circle.smul_def,
            Real.fourierChar_apply,smul_eq_mul]
          congr 1
          congr 1
          push_cast
          field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
        · simp only [indicator_of_notMem hu,smul_zero]
      _ = _ := integral_indicator measurableSet_Ici
  change Tendsto (fun x : ℝ => ∫ u : ℝ,
    Real.fourierChar (-(u*(-x/(2*Real.pi)))) • g u) (cocompact ℝ) (𝓝 0) at hrl
  simpa only [he] using hrl

theorem half_line_genuine_and_decay (f : ℝ → ℂ) (hf : Integrable f halfLine) :
    Integrable f halfLine ∧
      Tendsto (fun x : ℝ => ∫ u : ℝ, Complex.exp (I*(u : ℂ)*(x : ℂ))*f u ∂halfLine)
        (cocompact ℝ) (𝓝 0) :=
  ⟨hf,half_line_decay f⟩

theorem jet_real_genuine_and_decay (a : ℝ) (ha : 0 ≤ a) (j : ℕ) (t : ℝ) :
    (∀ x : ℝ, Integrable (integrand a j t (x : ℂ)) halfLine) ∧
      Tendsto (fun x : ℝ => jet a j t (x : ℂ)) (cocompact ℝ) (𝓝 0) := by
  refine ⟨fun x => integrand_integrable a ha j t (x : ℂ),?_⟩
  have he (x : ℝ) : jet a j t (x : ℂ) =
      ∫ u : ℝ, Complex.exp (I*(u : ℂ)*(x : ℂ))*integrand a j t 0 u ∂halfLine := by
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [integrand,mul_zero,Complex.exp_zero,mul_one]
    ring
  simpa only [← he] using half_line_decay (integrand a j t 0)

theorem flow_real_genuine_and_decay (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    (∀ x : ℝ, Integrable (fun u : ℝ => (weighted a 0 t 0 u : ℂ)*
      Complex.cos ((u : ℂ)*(x : ℂ))) halfLine) ∧
      Tendsto (fun x : ℝ => flow a t (x : ℂ)) (cocompact ℝ) (𝓝 0) := by
  refine ⟨fun x => cosine_integrable a ha t (x : ℂ),?_⟩
  have hj := (jet_real_genuine_and_decay a ha 0 t).2
  have hn : Tendsto (fun x : ℝ => -x) (cocompact ℝ) (cocompact ℝ) := by
    apply tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ)
    simpa [Real.dist_eq] using tendsto_dist_right_cocompact_atTop (0 : ℝ)
  have hh := (hj.add (hj.comp hn)).div_const (2 : ℂ)
  simpa only [Function.comp_apply,Complex.ofReal_neg,zero_add,zero_div,flow] using hh

theorem flow_not_polynomial_on_real_axis (a : ℝ) (ha : 0 ≤ a) (t : ℝ) :
    ¬ ∃ p : ℂ[X], ∀ x : ℝ, p.eval (x : ℂ) = flow a t (x : ℂ) := by
  rintro ⟨p,hp⟩
  have hdecay := (flow_real_genuine_and_decay a ha t).2.mono_left
    (atTop_le_cocompact : atTop ≤ cocompact ℝ)
  have hlim : Tendsto (fun x : ℝ => p.eval (x : ℂ)) atTop (𝓝 0) := by
    simpa only [hp] using hdecay
  by_cases hd : 0 < p.degree
  · have hn : Tendsto (fun x : ℝ => ‖(x : ℂ)‖) atTop atTop := by
      simpa only [Complex.norm_real,Real.norm_eq_abs] using tendsto_abs_atTop_atTop
    have hlarge := p.tendsto_norm_atTop hd hn
    have hsmall : Tendsto (fun x : ℝ => ‖p.eval (x : ℂ)‖) atTop (𝓝 0) := by
      simpa only [norm_zero] using hlim.norm
    exact not_tendsto_nhds_of_tendsto_atTop hlarge 0 hsmall
  · have he := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    have hconst (x : ℝ) : p.eval (x : ℂ) = p.coeff 0 := by
      nth_rw 1 [he]
      exact eval_C
    have hc : Tendsto (fun _ : ℝ => p.coeff 0) atTop (𝓝 0) := by
      simpa only [hconst] using hlim
    have hc0 : p.coeff 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hc
    have hp0 := hp 0
    rw [he,eval_C,hc0] at hp0
    have hz : flow a t 0 = 0 := by
      simpa only [Complex.ofReal_zero] using hp0.symm
    have hpos := actual_flow_zero_pos a ha t
    rw [hz,Complex.zero_re] at hpos
    linarith

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderFourierDecay
