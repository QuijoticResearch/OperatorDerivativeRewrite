import Foundation.RiemannEvenUniformFarScale
import Foundation.RiemannSixthFarConstruction

/-! Genuine sixth-order far saddles above a stationary-scale cutoff that
is uniform in time. No integral dominance or zero conclusion is asserted. -/
noncomputable section
open Set Filter Metric Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthUniformFarSaddles
open RiemannEvenRealSaddle RiemannEvenDomain RiemannEvenModelPhase RiemannEvenSaddleBranch
open RiemannQuarticTransitionSaddle RiemannSixthFarConstruction

theorem exists_uniform_actual_far_saddles :
    ∃ K : ℝ, 0 < K ∧ ∀ t u x : ℝ, 1 ≤ t → 120021 ≤ u → phaseSlope 3 t u = 0 →
      K*realScale u ≤ x → ∃ v : ℂ, complexSlope 3 t v = -(Complex.I*(x : ℂ)) ∧
      HasDerivAt (fun q : ℂ => Complex.exp ((t : ℂ)*q^6+Complex.I*(x : ℂ)*q)*
        RiemannThetaComplexKernel.kernelComplex q) 0 v ∧
      Complex.exp ((t : ℂ)*v^6+Complex.I*(x : ℂ)*v)*RiemannThetaComplexKernel.kernelComplex v ≠ 0 := by
  obtain ⟨D,hD,hscale⟩ := RiemannEvenUniformFarScale.exists_uniform_stationary_far_scale 3 (by norm_num)
  refine ⟨Real.exp (4*D),Real.exp_pos _,?_⟩
  intro t u x ht hu hs hx
  obtain ⟨a,ha,hxscale⟩ := RiemannEvenUniformFarScale.far_parameter u D x hx
  have huN : (((2*3 : ℕ) : ℝ)+4) ≤ u := by norm_num; linarith
  have hsc := hscale t u a ht huN hs ha
  norm_num at hsc
  have ha' : 120021 ≤ a := by linarith
  obtain ⟨w,v,hw,hmodel,hv,hactual,hdom,hkernel⟩ := constructed_actual_far_saddles t a ht ha' hsc
  change x = 4*Real.pi*Real.exp (4*a) at hxscale
  rw [← hxscale] at hactual
  have hcrit := actual_weight_critical t (x : ℂ) v hdom hkernel hactual
  exact ⟨v,hactual,hcrit⟩

theorem anchor_model_geometry (a : ℝ) (ha : 120021 ≤ a) (w : ℂ)
    (hw : w ∈ closedBall (RiemannQuarticFarModelSaddle.anchor a) (1/1024)) :
    120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧ ‖w‖+1 ≤ a+4 := by
  have hd : ‖w-RiemannQuarticFarModelSaddle.anchor a‖ ≤ (1/1024 : ℝ) := by
    simpa only [mem_closedBall,dist_eq_norm] using hw
  have hr := (Complex.abs_re_le_norm (w-RiemannQuarticFarModelSaddle.anchor a)).trans hd
  have hreal : (RiemannQuarticFarModelSaddle.anchor a).re = a := by simp [RiemannQuarticFarModelSaddle.anchor]
  simp only [Complex.sub_re,hreal] at hr
  have hi := (RiemannQuarticFarModelSaddle.far_saddle_geometry a (by linarith) w hw).2
  have hn := norm_add_le (w-RiemannQuarticFarModelSaddle.anchor a) (RiemannQuarticFarModelSaddle.anchor a)
  rw [sub_add_cancel] at hn
  have hb := RiemannQuarticFarModelSaddle.anchor_norm a (by linarith)
  exact ⟨by linarith [(abs_le.mp hr).1],hi,by linarith⟩

theorem exists_uniform_actual_far_frequency_disks :
    ∃ K : ℝ, 0 < K ∧ ∀ t u x : ℝ, 1 ≤ t → 120021 ≤ u → phaseSlope 3 t u = 0 →
      K*realScale u ≤ x → ∃ w : ℂ, 10000 ≤ x ∧ 120020 ≤ w.re ∧ |w.im| ≤ 1/2 ∧
      10000*(t*(‖w‖+1)^5+1) ≤ x ∧ modelDerivative 3 t w = -(Complex.I*(x : ℂ)) ∧
      ∀ z : ℂ, ‖z-(x : ℂ)‖ ≤ 1 →
        ∃! v, v ∈ closedBall w (1/x) ∧ complexSlope 3 t v = -(Complex.I*z) := by
  obtain ⟨D,hD,hscale⟩ := RiemannEvenUniformFarScale.exists_uniform_stationary_far_scale 3 (by norm_num)
  refine ⟨Real.exp (4*D),Real.exp_pos _,?_⟩
  intro t u x ht hu hs hx
  obtain ⟨a,ha,hxscale⟩ := RiemannEvenUniformFarScale.far_parameter u D x hx
  have huN : (((2*3 : ℕ) : ℝ)+4) ≤ u := by norm_num; linarith
  have hsc := hscale t u a ht huN hs ha
  norm_num at hsc
  have ha' : 120021 ≤ a := by linarith
  obtain ⟨w,v,hw,hmodel,hv,hactual,hdom,hkernel⟩ := constructed_actual_far_saddles t a ht ha' hsc
  change x = 4*Real.pi*Real.exp (4*a) at hxscale
  rw [← hxscale] at hmodel
  obtain ⟨hr,hi,hnorm⟩ := anchor_model_geometry a ha' w hw
  have hp : 10000*(t*(‖w‖+1)^5+1) ≤ x := by
    have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ ‖w‖+1) hnorm 5
    have ht0 : 0 ≤ t := by linarith
    have hm := mul_le_mul_of_nonneg_left hpow ht0
    have h1 : 1 ≤ (a+4)^5 := one_le_pow₀ (by linarith : 1 ≤ a+4)
    change 490000*(t+1)*(a+4)^5 ≤ 4*Real.pi*Real.exp (4*a) at hsc
    rw [← hxscale] at hsc
    nlinarith
  have hxlarge : 10000 ≤ x := by
    have hh : 0 ≤ t*(‖w‖+1)^5 := by positivity
    nlinarith
  exact ⟨w,hxlarge,hr,hi,hp,hmodel,fun z hz => RiemannSixthFarCorrection.actual_far_frequency_disk
    t x ht hxlarge w hr hi hp hmodel z hz⟩

theorem eventually_uniform_actual_far_saddles :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ t : ℝ in atTop, ∀ u ∈ Ici (0 : ℝ),
      IsMaxOn (weighted 3 0 t 0) (Ici 0) u → ∀ x : ℝ, K*realScale u ≤ x →
      ∃ v : ℂ, complexSlope 3 t v = -(Complex.I*(x : ℂ)) ∧
      HasDerivAt (fun q : ℂ => Complex.exp ((t : ℂ)*q^6+Complex.I*(x : ℂ)*q)*
        RiemannThetaComplexKernel.kernelComplex q) 0 v ∧
      Complex.exp ((t : ℂ)*v^6+Complex.I*(x : ℂ)*v)*RiemannThetaComplexKernel.kernelComplex v ≠ 0 := by
  obtain ⟨K,hK,hfar⟩ := exists_uniform_actual_far_saddles
  refine ⟨K,hK,?_⟩
  filter_upwards [maxima_escape 3 (by norm_num) 120021 (by norm_num),eventually_ge_atTop (1 : ℝ)] with t he ht
  intro u hu hmax x hx
  have hlarge := he u hu hmax
  have hs := max_real_stationary 3 t u (by linarith) hmax
  exact hfar t u x ht hlarge.le hs hx

end OperatorDerivativeRewrite.Foundation.RiemannSixthUniformFarSaddles
