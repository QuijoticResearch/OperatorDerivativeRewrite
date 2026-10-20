import Foundation.RiemannQuarticFarGaussianPhase
import Foundation.RiemannQuarticReality
/-! Actual far-frequency real zeros from verified arithmetic contour asymptotics.
Real sign changes do not assert simplicity or exclude nonreal zeros. -/
noncomputable section
open Set Metric Complex Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarRealZeros
open RiemannQuarticFarGaussianPhase RiemannQuarticFarAnalyticBranch RiemannQuarticFarPairing
open RiemannQuarticFarGaussianLimit RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch

theorem cos_arg_mul_exp (a p : ℂ) (ha : a ≠ 0) :
    Real.cos (a*Complex.exp p).arg=Real.cos (a.arg+p.im) := by
  rw [Complex.cos_arg (mul_ne_zero ha (Complex.exp_ne_zero p)),Real.cos_add,
    Complex.cos_arg ha,Complex.sin_arg,norm_mul,Complex.norm_exp,Complex.mul_re,
    Complex.exp_re,Complex.exp_im]
  field_simp [norm_ne_zero_iff.mpr ha,(Real.exp_pos p.re).ne']

section FarData
variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
  (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
include ht hx hr hi hp hs
local notation "B" => RiemannQuarticFarAnalyticBranch.branch t x ht hx w hr hi hp hs

theorem actual_real_sign_change
    (herror : ∀ y ∈ Icc x (x+1/2),
      |(RiemannQuarticFlow.flow t (y : ℂ)).re/‖modelGaussianAmplitude t (y : ℂ) (B (y : ℂ))‖-
        Real.cos (modelGaussianAmplitude t (y : ℂ) (B (y : ℂ))).arg| ≤ 1/4) :
    ∃ a b : ℝ, x ≤ a ∧ a < b ∧ b ≤ x+1/2 ∧
      0 < (RiemannQuarticFlow.flow t (a : ℂ)).re ∧ (RiemannQuarticFlow.flow t (b : ℂ)).re < 0 := by
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
  have hpos : 0 < (RiemannQuarticFlow.flow t (a : ℂ)).re := by
    have hq : 0 < (RiemannQuarticFlow.flow t (a : ℂ)).re/
        ‖modelGaussianAmplitude t (a : ℂ) (B (a : ℂ))‖ := by linarith [(abs_le.mp hpa).1]
    simpa using (lt_div_iff₀ (hAy a ha)).mp hq
  have hneg : (RiemannQuarticFlow.flow t (b : ℂ)).re < 0 := by
    have hq : (RiemannQuarticFlow.flow t (b : ℂ)).re/
        ‖modelGaussianAmplitude t (b : ℂ) (B (b : ℂ))‖ < 0 := by linarith [(abs_le.mp hnb).2]
    simpa using (div_lt_iff₀ (hAy b hb)).mp hq
  exact ⟨a,b,ha.1,hab,hb.2,hpos,hneg⟩

end FarData

theorem eventually_actual_real_sign_change (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, ∃ a b : ℝ, x ≤ a ∧ a < b ∧ b ≤ x+1/2 ∧
      0 < (RiemannQuarticFlow.flow t (a : ℂ)).re ∧ (RiemannQuarticFlow.flow t (b : ℂ)).re < 0 := by
  filter_upwards [eventually_controlled_far_saddles t ht,
    eventually_uniform_real_flow_error (1/4) (by norm_num)] with x hdata he
  obtain ⟨hx,w,v₀,hr,hi,hp,hs,hv₀,hz₀,hvre,hvim,hkn⟩ := hdata
  apply actual_real_sign_change t x ht hx w hr hi hp hs
  intro y hy
  have hy' : ‖(y : ℂ)-(x : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_le]
    constructor <;> linarith [hy.1,hy.2]
  have hb := branch_spec t x ht hx w hr hi hp hs (y : ℂ) hy'
  exact (he t ht w (RiemannQuarticFarAnalyticBranch.branch t x ht hx w hr hi hp hs (y : ℂ))
    hr hi hp hs (by simpa only [mem_closedBall,dist_eq_norm] using hb.1) y hb.2).2.2

theorem eventually_actual_real_zero (t : ℝ) (ht : 1 ≤ t) :
    ∀ᶠ x : ℝ in atTop, ∃ y ∈ Ioo x (x+1/2), RiemannQuarticFlow.flow t (y : ℂ)=0 := by
  filter_upwards [eventually_actual_real_sign_change t ht] with x hsign
  obtain ⟨a,b,hxa,hab,hbx,hpos,hneg⟩ := hsign
  let f := fun y : ℝ => (RiemannQuarticFlow.flow t (y : ℂ)).re
  have hc : Continuous f := Complex.continuous_re.comp
    ((RiemannQuarticFlow.flow_differentiable t).continuous.comp Complex.continuous_ofReal)
  obtain ⟨y,hy,hyzero⟩ := intermediate_value_Icc' hab.le hc.continuousOn ⟨hneg.le,hpos.le⟩
  have hya : y ≠ a := by
    intro h
    rw [h] at hyzero
    change (RiemannQuarticFlow.flow t (a : ℂ)).re=0 at hyzero
    linarith
  have hyb : y ≠ b := by
    intro h
    rw [h] at hyzero
    change (RiemannQuarticFlow.flow t (b : ℂ)).re=0 at hyzero
    linarith
  have hay : a < y := lt_of_le_of_ne hy.1 hya.symm
  have hyb' : y < b := lt_of_le_of_ne hy.2 hyb
  refine ⟨y,⟨lt_of_le_of_lt hxa hay,lt_of_lt_of_le hyb' hbx⟩,?_⟩
  apply Complex.ext
  · exact hyzero
  · exact RiemannQuarticReality.flow_im_zero t y

theorem arbitrarily_large_actual_real_zero (t : ℝ) (ht : 1 ≤ t) (R : ℝ) :
    ∃ y : ℝ, R < y ∧ RiemannQuarticFlow.flow t (y : ℂ)=0 := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp (eventually_actual_real_zero t ht)
  obtain ⟨y,hy,hzero⟩ := hX (max X R) (le_max_left X R)
  exact ⟨y,lt_of_le_of_lt (le_max_right X R) hy.1,hzero⟩

theorem real_zeros_not_bddAbove (t : ℝ) (ht : 1 ≤ t) :
    ¬BddAbove {y : ℝ | RiemannQuarticFlow.flow t (y : ℂ)=0} := by
  rintro ⟨R,hR⟩
  obtain ⟨y,hy,hzero⟩ := arbitrarily_large_actual_real_zero t ht R
  exact (not_lt_of_ge (hR hzero)) hy

theorem infinitely_many_actual_real_zeros (t : ℝ) (ht : 1 ≤ t) :
    {y : ℝ | RiemannQuarticFlow.flow t (y : ℂ)=0}.Infinite :=
  Set.infinite_of_not_bddAbove (real_zeros_not_bddAbove t ht)

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarRealZeros
