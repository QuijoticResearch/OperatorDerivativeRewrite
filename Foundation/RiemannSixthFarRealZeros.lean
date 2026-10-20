import Foundation.RiemannSixthFarGaussianPhase
import Foundation.RiemannQuarticFarRealZeros
/-! Actual sixth-order far-frequency real sign changes and zeros.
These assertions do not exclude nonreal zeros or prove simplicity. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannSixthFarRealZeros
open RiemannSixthFarGaussianPhase RiemannSixthFarAnalyticBranch RiemannSixthFarPairing
open RiemannEvenModelPhase
open RiemannQuarticFarRealZeros (cos_arg_mul_exp)

section FarData
variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 10000*(t*(‖w‖+1)^5+1) ≤ x)
  (hs : modelDerivative 3 t w= -(Complex.I*(x : ℂ)))
include ht hx hr hi hp hs
local notation "B" => RiemannSixthFarAnalyticBranch.branch t x ht hx w hr hi hp hs

theorem actual_real_sign_change
    (herror : ∀ y ∈ Icc x (x+1/2),
      |(RiemannEvenFlow.flow 3 t (y : ℂ)).re/‖modelGaussianAmplitude t (y : ℂ) (B (y : ℂ))‖-
        Real.cos (modelGaussianAmplitude t (y : ℂ) (B (y : ℂ))).arg| ≤ 1/4) :
    ∃ a b : ℝ, x ≤ a ∧ a < b ∧ b ≤ x+1/2 ∧
      0 < (RiemannEvenFlow.flow 3 t (a : ℂ)).re ∧ (RiemannEvenFlow.flow 3 t (b : ℂ)).re < 0 := by
  obtain ⟨P,hP0,hP⟩ := exists_normalized_amplitude_phase t x ht hx w hr hi hp hs
  let A₀ := modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))
  let θ := fun y : ℝ => A₀.arg+(P (y : ℂ)).im
  have hnear (y : ℝ) (hy : y ∈ Icc x (x+1/2)) : ‖(y : ℂ)-(x : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [hy.1,hy.2]
  have hopen (y : ℝ) (hy : y ∈ Icc x (x+1/2)) : y ∈ Ioo (x-1) (x+1) := by
    constructor <;> linarith [hy.1,hy.2]
  have hcont : ContinuousOn θ (Icc x (x+1/2)) := by
    intro y hy
    have hyball : (y : ℂ) ∈ ball (x : ℂ) 1 := by
      simpa only [mem_ball,dist_eq_norm] using hnear y hy
    have hc : ContinuousAt (fun a : ℝ => (P (a : ℂ)).im) y :=
      Complex.continuous_im.continuousAt.comp
        ((hP (y : ℂ) hyball).continuousAt.comp Complex.continuous_ofReal.continuousAt)
    exact (continuousAt_const.add hc).continuousWithinAt
  have hg := amplitude_phase_real_growth t x ht hx w hr hi hp hs P hP x (x+1/2)
    (by constructor <;> linarith) (by constructor <;> linarith) (by linarith)
  rw [hP0,Complex.zero_im,sub_zero] at hg
  have hstart : θ x ≤ 2*Real.pi := by
    dsimp [θ]
    rw [hP0,Complex.zero_im,add_zero]
    linarith [Complex.arg_le_pi A₀,Real.pi_pos]
  have hend : 3*Real.pi ≤ θ (x+1/2) := by
    dsimp [θ]
    linarith [Complex.neg_pi_lt_arg A₀,Real.pi_lt_four]
  obtain ⟨a,ha,hθa⟩ := intermediate_value_Icc (by linarith : x ≤ x+1/2) hcont
    (show 2*Real.pi ∈ Icc (θ x) (θ (x+1/2)) by constructor <;> linarith [Real.pi_pos])
  obtain ⟨b,hb,hθb⟩ := intermediate_value_Icc (by linarith : x ≤ x+1/2) hcont
    (show 3*Real.pi ∈ Icc (θ x) (θ (x+1/2)) by constructor <;> linarith [Real.pi_pos])
  have hab : a < b := by
    by_contra h
    have hba : b ≤ a := le_of_not_gt h
    have hg' := amplitude_phase_real_growth t x ht hx w hr hi hp hs P hP b a (hopen b hb) (hopen a ha) hba
    change A₀.arg+(P (a : ℂ)).im=2*Real.pi at hθa
    change A₀.arg+(P (b : ℂ)).im=3*Real.pi at hθb
    nlinarith [Real.pi_pos]
  have hA₀ : A₀ ≠ 0 := by
    exact modelGaussianAmplitude_ne_zero t x ht hx w (B (x : ℂ)) hr hi hp hs
      (by simpa only [mem_closedBall,dist_eq_norm] using
        (branch_spec t x ht hx w hr hi hp hs (x : ℂ) (by simp)).1) (x : ℂ)
  have hcos (y : ℝ) (hy : y ∈ Icc x (x+1/2)) :
      Real.cos (modelGaussianAmplitude t (y : ℂ) (B (y : ℂ))).arg=Real.cos (θ y) := by
    rw [amplitude_eq_exp_phase t x ht hx w hr hi hp hs P hP0 hP (y : ℂ) (hnear y hy)]
    exact cos_arg_mul_exp A₀ (P (y : ℂ)) hA₀
  have hAy (y : ℝ) (hy : y ∈ Icc x (x+1/2)) :
      0 < ‖modelGaussianAmplitude t (y : ℂ) (B (y : ℂ))‖ := by
    apply norm_pos_iff.mpr
    exact modelGaussianAmplitude_ne_zero t x ht hx w (B (y : ℂ)) hr hi hp hs
      (by simpa only [mem_closedBall,dist_eq_norm] using
        (branch_spec t x ht hx w hr hi hp hs (y : ℂ) (hnear y hy).le).1) (y : ℂ)
  have hpa := herror a ha
  have hnb := herror b hb
  rw [hcos a ha,hθa,Real.cos_two_pi] at hpa
  have hcos3 : Real.cos (3*Real.pi)= -1 := by
    rw [show 3*Real.pi=2*Real.pi+Real.pi by ring,Real.cos_add]
    simp
  rw [hcos b hb,hθb,hcos3] at hnb
  have hpos : 0 < (RiemannEvenFlow.flow 3 t (a : ℂ)).re := by
    have hq : 0 < (RiemannEvenFlow.flow 3 t (a : ℂ)).re/
        ‖modelGaussianAmplitude t (a : ℂ) (B (a : ℂ))‖ := by linarith [(abs_le.mp hpa).1]
    simpa using (lt_div_iff₀ (hAy a ha)).mp hq
  have hneg : (RiemannEvenFlow.flow 3 t (b : ℂ)).re < 0 := by
    have hq : (RiemannEvenFlow.flow 3 t (b : ℂ)).re/
        ‖modelGaussianAmplitude t (b : ℂ) (B (b : ℂ))‖ < 0 := by linarith [(abs_le.mp hnb).2]
    simpa using (div_lt_iff₀ (hAy b hb)).mp hq
  exact ⟨a,b,ha.1,hab,hb.2,hpos,hneg⟩

end FarData

theorem exists_uniform_actual_real_sign_change :
    ∃ K : ℝ, 0 < K ∧ ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ a b : ℝ, x ≤ a ∧ a < b ∧ b ≤ x+1/2 ∧
        0 < (RiemannEvenFlow.flow 3 t (a : ℂ)).re ∧ (RiemannEvenFlow.flow 3 t (b : ℂ)).re < 0 := by
  obtain ⟨K,hK,hC⟩ := RiemannSixthUniformFarSaddles.exists_uniform_actual_far_frequency_disks
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventually_uniform_real_flow_error (1/4) (by norm_num))
  refine ⟨K,hK,X,?_⟩
  intro t u x ht hu hstat hx
  obtain ⟨w,hxl,hr,hi,hp,hs,hroots⟩ := hC t u x ht hu hstat ((le_max_right _ _).trans hx)
  apply actual_real_sign_change t x ht hxl w hr hi hp hs
  intro y hy
  have hy' : ‖(y : ℂ)-(x : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_le]
    constructor <;> linarith [hy.1,hy.2]
  have hb := branch_spec t x ht hxl w hr hi hp hs (y : ℂ) hy'
  exact (hX x ((le_max_left _ _).trans hx) t ht w
    (branch t x ht hxl w hr hi hp hs (y : ℂ)) hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hb.1) y hb.2).2.2

theorem actual_real_zero_of_sign_change (t x : ℝ)
    (hsign : ∃ a b : ℝ, x ≤ a ∧ a < b ∧ b ≤ x+1/2 ∧
      0 < (RiemannEvenFlow.flow 3 t (a : ℂ)).re ∧ (RiemannEvenFlow.flow 3 t (b : ℂ)).re < 0) :
    ∃ y ∈ Ioo x (x+1/2), RiemannEvenFlow.flow 3 t (y : ℂ)=0 := by
  obtain ⟨a,b,hxa,hab,hbx,hpos,hneg⟩ := hsign
  let f := fun y : ℝ => (RiemannEvenFlow.flow 3 t (y : ℂ)).re
  have hc : Continuous f := Complex.continuous_re.comp
    ((RiemannEvenFlow.flow_differentiable 3 t).continuous.comp Complex.continuous_ofReal)
  obtain ⟨y,hy,hyzero⟩ := intermediate_value_Icc' hab.le hc.continuousOn ⟨hneg.le,hpos.le⟩
  have hya : y ≠ a := by
    intro h
    rw [h] at hyzero
    change (RiemannEvenFlow.flow 3 t (a : ℂ)).re=0 at hyzero
    linarith
  have hyb : y ≠ b := by
    intro h
    rw [h] at hyzero
    change (RiemannEvenFlow.flow 3 t (b : ℂ)).re=0 at hyzero
    linarith
  have hay : a < y := lt_of_le_of_ne hy.1 hya.symm
  have hyb' : y < b := lt_of_le_of_ne hy.2 hyb
  refine ⟨y,⟨lt_of_le_of_lt hxa hay,lt_of_lt_of_le hyb' hbx⟩,?_⟩
  apply Complex.ext
  · exact hyzero
  · rw [RiemannEvenHorizontalPairing.flow_real_horizontal 3 t y 0 (by norm_num; positivity)]
    rfl

theorem exists_uniform_actual_real_zero :
    ∃ K : ℝ, 0 < K ∧ ∃ X : ℝ, ∀ t u x : ℝ,
      1 ≤ t → 120021 ≤ u → RiemannEvenRealSaddle.phaseSlope 3 t u = 0 →
      max X (K*RiemannQuarticTransitionSaddle.realScale u) ≤ x →
      ∃ y ∈ Ioo x (x+1/2), RiemannEvenFlow.flow 3 t (y : ℂ)=0 := by
  obtain ⟨K,hK,X,hX⟩ := exists_uniform_actual_real_sign_change
  exact ⟨K,hK,X,fun t u x ht hu hs hx => actual_real_zero_of_sign_change t x (hX t u x ht hu hs hx)⟩

theorem eventually_actual_real_zero :
    ∀ᶠ t : ℝ in atTop, ∀ᶠ x : ℝ in atTop,
      ∃ y ∈ Ioo x (x+1/2), RiemannEvenFlow.flow 3 t (y : ℂ)=0 := by
  obtain ⟨K,hK,X,hX⟩ := exists_uniform_actual_real_zero
  filter_upwards [RiemannEvenRealSaddle.maxima_escape 3 (by norm_num) 120021 (by norm_num),
    eventually_ge_atTop (1 : ℝ)] with t he ht
  obtain ⟨u,hu,hmax⟩ := RiemannEvenRealSaddle.exists_global_max 3 t
  have hlarge := he u hu hmax
  have hs := RiemannEvenRealSaddle.max_real_stationary 3 t u (by linarith) hmax
  filter_upwards [eventually_ge_atTop (max X (K*RiemannQuarticTransitionSaddle.realScale u))] with x hx
  exact hX t u x ht hlarge.le hs hx

theorem eventually_arbitrarily_large_actual_real_zero :
    ∀ᶠ t : ℝ in atTop, ∀ R : ℝ, ∃ y : ℝ, R < y ∧ RiemannEvenFlow.flow 3 t (y : ℂ)=0 := by
  filter_upwards [eventually_actual_real_zero] with t he
  intro R
  obtain ⟨X,hX⟩ := eventually_atTop.mp he
  obtain ⟨y,hy,hzero⟩ := hX (max X R) (le_max_left X R)
  exact ⟨y,lt_of_le_of_lt (le_max_right X R) hy.1,hzero⟩

theorem eventually_infinitely_many_actual_real_zeros :
    ∀ᶠ t : ℝ in atTop, {y : ℝ | RiemannEvenFlow.flow 3 t (y : ℂ)=0}.Infinite := by
  filter_upwards [eventually_arbitrarily_large_actual_real_zero] with t he
  apply Set.infinite_of_not_bddAbove
  rintro ⟨R,hR⟩
  obtain ⟨y,hy,hzero⟩ := he R
  exact (not_lt_of_ge (hR hzero)) hy

end OperatorDerivativeRewrite.Foundation.RiemannSixthFarRealZeros
