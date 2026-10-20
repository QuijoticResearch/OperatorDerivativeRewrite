import Foundation.RiemannQuarticFarComplexPairing
import Foundation.RiemannQuarticZeroStrip
import Foundation.RiemannQuarticNormalizedAnalytic
import Mathlib.Analysis.Calculus.Deriv.Star
/-! Balanced analytic envelope and nonlinear cosine phase of the actual far pair.
A fixed center argument is used; no varying principal argument is differentiated. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarCosinePhase
open RiemannQuarticFarComplexPairing RiemannQuarticFarGaussianPhase RiemannQuarticFarAnalyticBranch
open RiemannQuarticFarPairing RiemannQuarticFarGaussianLimit RiemannQuarticSaddleTheta

def envelope (a : ℂ) (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  (‖a‖ : ℂ)*Complex.exp ((P z+conj (P (conj z)))/2)

def phase (a : ℂ) (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  (a.arg : ℂ)+(P z-conj (P (conj z)))/(2*Complex.I)

theorem split_exponentials (a : ℂ) (P : ℂ → ℂ) (z : ℂ) :
    envelope a P z*Complex.exp (phase a P z*Complex.I)=a*Complex.exp (P z) ∧
    envelope a P z*Complex.exp (-phase a P z*Complex.I)=conj a*Complex.exp (conj (P (conj z))) := by
  have hplus : (P z+conj (P (conj z)))/2+phase a P z*Complex.I=(a.arg : ℂ)*Complex.I+P z := by
    dsimp [phase]
    field_simp <;> ring
  have hminus : (P z+conj (P (conj z)))/2+-phase a P z*Complex.I=
      -(a.arg : ℂ)*Complex.I+conj (P (conj z)) := by
    dsimp [phase]
    field_simp <;> ring
  have hpolar : (‖a‖ : ℂ)*Complex.exp (-(a.arg : ℂ)*Complex.I)=conj a := by
    have h := congrArg conj (Complex.norm_mul_exp_arg_mul_I a)
    simp only [map_mul,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I] at h
    convert h using 1 <;> congr 1 <;> ring
  constructor
  · calc
      _ = (‖a‖ : ℂ)*Complex.exp ((P z+conj (P (conj z)))/2+phase a P z*Complex.I) := by
        dsimp [envelope]
        rw [Complex.exp_add]
        ring
      _ = (‖a‖ : ℂ)*Complex.exp ((a.arg : ℂ)*Complex.I+P z) := by rw [hplus]
      _ = a*Complex.exp (P z) := by rw [Complex.exp_add,← mul_assoc,Complex.norm_mul_exp_arg_mul_I]
  · calc
      _ = (‖a‖ : ℂ)*Complex.exp ((P z+conj (P (conj z)))/2+-phase a P z*Complex.I) := by
        dsimp [envelope]
        rw [Complex.exp_add]
        ring
      _ = (‖a‖ : ℂ)*Complex.exp (-(a.arg : ℂ)*Complex.I+conj (P (conj z))) := by rw [hminus]
      _ = conj a*Complex.exp (conj (P (conj z))) := by rw [Complex.exp_add,← mul_assoc,hpolar]

theorem pair_identity (a : ℂ) (P : ℂ → ℂ) (z : ℂ) :
    (a*Complex.exp (P z)+conj a*Complex.exp (conj (P (conj z))))/2=
      envelope a P z*Complex.cos (phase a P z) := by
  have h := split_exponentials a P z
  rw [← h.1,← h.2,← mul_add,← Complex.two_cos]
  ring

theorem pair_norm_identity (a : ℂ) (P : ℂ → ℂ) (z : ℂ) :
    ‖a*Complex.exp (P z)‖+‖conj a*Complex.exp (conj (P (conj z)))‖=
      2*‖envelope a P z‖*Real.cosh (phase a P z).im := by
  have h := split_exponentials a P z
  rw [← h.1,← h.2,norm_mul,norm_mul,Complex.norm_exp,Complex.norm_exp]
  have h1 : (phase a P z*Complex.I).re= -(phase a P z).im := by simp [Complex.mul_re]
  have h2 : (-phase a P z*Complex.I).re=(phase a P z).im := by simp [Complex.mul_re]
  rw [h1,h2,Real.cosh_eq]
  ring

theorem envelope_ne_zero (a : ℂ) (ha : a ≠ 0) (P : ℂ → ℂ) (z : ℂ) : envelope a P z ≠ 0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)) (Complex.exp_ne_zero _)

theorem envelope_conj (a : ℂ) (P : ℂ → ℂ) (z : ℂ) : envelope a P (conj z)=conj (envelope a P z) := by
  simp only [envelope,map_mul,Complex.conj_ofReal,← Complex.exp_conj,map_div₀,map_add,
    Complex.conj_ofNat,Complex.conj_conj]
  congr 2
  ring

theorem phase_conj (a : ℂ) (P : ℂ → ℂ) (z : ℂ) : phase a P (conj z)=conj (phase a P z) := by
  simp only [phase,map_add,Complex.conj_ofReal,map_div₀,map_sub,map_mul,Complex.conj_ofNat,
    Complex.conj_I,Complex.conj_conj]
  field_simp <;> ring

theorem phase_real (a : ℂ) (P : ℂ → ℂ) (y : ℝ) : (phase a P (y : ℂ)).im=0 := by
  have h := congrArg Complex.im (phase_conj a P (y : ℂ))
  simp only [Complex.conj_ofReal,Complex.conj_im] at h
  linarith

theorem normalized_flow_conj (t : ℝ) (a : ℂ) (P : ℂ → ℂ) (z : ℂ) :
    RiemannQuarticFlow.flow t (conj z)/envelope a P (conj z)=
      conj (RiemannQuarticFlow.flow t z/envelope a P z) := by
  rw [RiemannQuarticNormalizedAnalytic.flow_conj,envelope_conj,map_div₀]

private theorem conjugate_disk (x : ℝ) (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ‖conj z-(x : ℂ)‖ < 1 := by
  have he : conj z-(x : ℂ)=conj (z-(x : ℂ)) := by simp
  rw [he,norm_conj]
  exact hz

section FarData
variable (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
  (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
  (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
  (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
  (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
  (hP : ∀ z ∈ ball (x : ℂ) 1,
    HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z)
include ht hx hr hi hp hs hP0 hP
local notation "B" => RiemannQuarticFarAnalyticBranch.branch t x ht hx w hr hi hp hs
local notation "A₀" => modelGaussianAmplitude t (x : ℂ) (B (x : ℂ))

private theorem center_ne_zero : A₀ ≠ 0 :=
  modelGaussianAmplitude_ne_zero t x ht hx w (B (x : ℂ)) hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using
      (branch_spec t x ht hx w hr hi hp hs (x : ℂ) (by simp)).1) (x : ℂ)

private theorem reflected_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasDerivAt (fun y => conj (P (conj y))) (conj (phaseSlope t x ht hx w hr hi hp hs (conj z))) z := by
  have hz' : conj z ∈ ball (x : ℂ) 1 := by
    simpa only [mem_ball,dist_eq_norm] using conjugate_disk x z hz
  have h := (hP (conj z) hz').conj_conj
  simpa only [Function.comp_def,Complex.conj_conj] using h

theorem actual_pair_identity (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    (modelGaussianAmplitude t z (B z)+conj (modelGaussianAmplitude t (conj z) (B (conj z))))/2=
      envelope A₀ P z*Complex.cos (phase A₀ P z) := by
  rw [amplitude_eq_exp_phase t x ht hx w hr hi hp hs P hP0 hP z hz,
    amplitude_eq_exp_phase t x ht hx w hr hi hp hs P hP0 hP (conj z) (conjugate_disk x z hz),
    map_mul,← Complex.exp_conj]
  exact pair_identity A₀ P z

theorem actual_pair_norm_identity (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ‖modelGaussianAmplitude t z (B z)‖+‖modelGaussianAmplitude t (conj z) (B (conj z))‖=
      2*‖envelope A₀ P z‖*Real.cosh (phase A₀ P z).im := by
  rw [amplitude_eq_exp_phase t x ht hx w hr hi hp hs P hP0 hP z hz,
    amplitude_eq_exp_phase t x ht hx w hr hi hp hs P hP0 hP (conj z) (conjugate_disk x z hz)]
  simpa only [Complex.exp_conj,← map_mul,norm_conj] using pair_norm_identity A₀ P z

theorem phase_hasDerivAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    HasDerivAt (phase A₀ P)
      ((phaseSlope t x ht hx w hr hi hp hs z-conj (phaseSlope t x ht hx w hr hi hp hs (conj z)))/
        (2*Complex.I)) z := by
  have hz' : z ∈ ball (x : ℂ) 1 := by simpa only [mem_ball,dist_eq_norm] using hz
  have h := (hasDerivAt_const z ((A₀).arg : ℂ)).add
    (((hP z hz').sub (reflected_hasDerivAt t x ht hx w hr hi hp hs P hP0 hP z hz)).div_const (2*Complex.I))
  convert h using 1
  · funext y
    rfl
  · simp only [zero_add]

theorem envelope_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) : AnalyticAt ℂ (envelope A₀ P) z := by
  have hd : DifferentiableOn ℂ (envelope A₀ P) (ball (x : ℂ) 1) := by
    intro y hy
    have hy' : ‖y-(x : ℂ)‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hy
    have h := ((((hP y hy).add (reflected_hasDerivAt t x ht hx w hr hi hp hs P hP0 hP y hy')).div_const
      (2 : ℂ)).cexp.const_mul (‖A₀‖ : ℂ)).differentiableAt
    exact h.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

theorem phase_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) : AnalyticAt ℂ (phase A₀ P) z := by
  have hd : DifferentiableOn ℂ (phase A₀ P) (ball (x : ℂ) 1) := by
    intro y hy
    exact (phase_hasDerivAt t x ht hx w hr hi hp hs P hP0 hP y
      (by simpa only [mem_ball,dist_eq_norm] using hy)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (isOpen_ball.mem_nhds (by simpa only [mem_ball,dist_eq_norm] using hz))

theorem normalized_flow_analyticAt (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    AnalyticAt ℂ (fun y => RiemannQuarticFlow.flow t y/envelope A₀ P y) z :=
  ((RiemannQuarticFlow.flow_differentiable t).analyticAt z).div
    (envelope_analyticAt t x ht hx w hr hi hp hs P hP0 hP z hz)
    (envelope_ne_zero A₀ (center_ne_zero t x ht hx w hr hi hp hs P hP0 hP) P z)

theorem phase_deriv_model_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    ‖deriv (phase A₀ P) z-(w.re : ℂ)‖ ≤ 513/x := by
  have hS (y : ℂ) (hy : ‖y-(x : ℂ)‖ < 1) :
      ‖phaseSlope t x ht hx w hr hi hp hs y-Complex.I*w‖ ≤ 513/x := by
    have he := phaseSlope_error_bound t x ht hx w hr hi hp hs y hy
    have hb : ‖B y-w‖ ≤ 1/x := by
      simpa only [mem_closedBall,dist_eq_norm] using (branch_spec t x ht hx w hr hi hp hs y hy.le).1
    have htri := norm_add_le (phaseSlope t x ht hx w hr hi hp hs y-Complex.I*(B y)) (Complex.I*(B y-w))
    rw [show phaseSlope t x ht hx w hr hi hp hs y-Complex.I*(B y)+Complex.I*(B y-w)=
      phaseSlope t x ht hx w hr hi hp hs y-Complex.I*w by ring] at htri
    simp only [norm_mul,Complex.norm_I,one_mul] at htri
    calc
      _ ≤ 512/x+1/x := htri.trans (add_le_add he hb)
      _ = 513/x := by ring
  rw [(phase_hasDerivAt t x ht hx w hr hi hp hs P hP0 hP z hz).deriv]
  have hid : (phaseSlope t x ht hx w hr hi hp hs z-conj (phaseSlope t x ht hx w hr hi hp hs (conj z)))/
      (2*Complex.I)-(w.re : ℂ)=
      ((phaseSlope t x ht hx w hr hi hp hs z-Complex.I*w)-
        conj (phaseSlope t x ht hx w hr hi hp hs (conj z)-Complex.I*w))/(2*Complex.I) := by
    rw [Complex.re_eq_add_conj]
    simp only [map_sub,map_mul,Complex.conj_I]
    field_simp <;> ring
  rw [hid,norm_div,norm_mul,Complex.norm_ofNat,Complex.norm_I,mul_one]
  have htri := norm_sub_le (phaseSlope t x ht hx w hr hi hp hs z-Complex.I*w)
    (conj (phaseSlope t x ht hx w hr hi hp hs (conj z)-Complex.I*w))
  rw [norm_conj] at htri
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  linarith [hS z hz,hS (conj z) (conjugate_disk x z hz)]

theorem phase_im_lower_bound (z : ℂ) (hz : ‖z-(x : ℂ)‖ < 1) :
    w.re*|z.im| ≤ 2*|(phase A₀ P z).im| := by
  let r := (1+‖z-(x : ℂ)‖)/2
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hzr : ‖z-(x : ℂ)‖ ≤ r := by dsimp [r]; linarith
  have hnear (y : ℂ) (hy : y ∈ closedBall (x : ℂ) r) : ‖y-(x : ℂ)‖ < 1 := by
    have hy' : ‖y-(x : ℂ)‖ ≤ r := by simpa only [mem_closedBall,dist_eq_norm] using hy
    exact hy'.trans_lt hr1
  have hd : ∀ y ∈ closedBall (x : ℂ) r, DifferentiableAt ℂ (phase A₀ P) y := by
    intro y hy
    exact (phase_analyticAt t x ht hx w hr hi hp hs P hP0 hP y (hnear y hy)).differentiableAt
  have hb : ∀ y ∈ closedBall (x : ℂ) r,
      ‖deriv (phase A₀ P) y-(w.re : ℂ)‖ ≤ ‖(w.re : ℂ)‖/2 := by
    intro y hy
    have h := phase_deriv_model_bound t x ht hx w hr hi hp hs P hP0 hP y (hnear y hy)
    have hsx : 513/x ≤ 1 := (div_le_iff₀ (by linarith : 0 < x)).mpr (by linarith)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < w.re)]
    exact h.trans (hsx.trans (by linarith))
  have hzc : ‖conj z-(x : ℂ)‖=‖z-(x : ℂ)‖ := by
    have he : conj z-(x : ℂ)=conj (z-(x : ℂ)) := by simp
    rw [he,norm_conj]
  have h := RiemannQuarticFrequencyBranch.scalar_ball_lower_bound (phase A₀ P) (x : ℂ)
    (w.re : ℂ) r hd hb z (conj z)
    (by simpa only [mem_closedBall,dist_eq_norm] using hzr)
    (by simpa only [mem_closedBall,dist_eq_norm,hzc] using hzr)
  have hn (q : ℂ) : ‖q-conj q‖=2*|q.im| := by
    have he : q-conj q=(2*(q.im : ℂ))*Complex.I := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring
    rw [he,norm_mul,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
  rw [phase_conj,hn,hn,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < w.re)] at h
  nlinarith

end FarData
theorem eventually_uniform_normalized_cosine_error (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (t : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
      (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
      (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
      (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
      (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z),
      let a := modelGaussianAmplitude t (x : ℂ) (branch t x ht hx w hr hi hp hs (x : ℂ))
      ∀ z : ℂ, ‖z-(x : ℂ)‖ < 1 →
        ‖RiemannQuarticFlow.flow t z/envelope a P z-Complex.cos (phase a P z)‖ ≤ ε*Real.cosh (phase a P z).im := by
  filter_upwards [eventually_uniform_complex_pair_error (ε/2) (by positivity)] with x he
  intro t ht hx w hr hi hp hs P hP0 hP
  dsimp only
  intro z hz
  let a := modelGaussianAmplitude t (x : ℂ) (branch t x ht hx w hr hi hp hs (x : ℂ))
  have han := center_ne_zero t x ht hx w hr hi hp hs P hP0 hP
  have hEn := envelope_ne_zero a han P z
  have hpair := actual_pair_identity t x ht hx w hr hi hp hs P hP0 hP z hz
  have hnorm := actual_pair_norm_identity t x ht hx w hr hi hp hs P hP0 hP z hz
  have h := he t ht hx w hr hi hp hs z hz.le
  rw [hpair,hnorm] at h
  have hfrac : RiemannQuarticFlow.flow t z/envelope a P z-Complex.cos (phase a P z)=
      (RiemannQuarticFlow.flow t z-envelope a P z*Complex.cos (phase a P z))/envelope a P z := by field_simp
  change ‖RiemannQuarticFlow.flow t z/envelope a P z-Complex.cos (phase a P z)‖ ≤ ε*Real.cosh (phase a P z).im
  rw [hfrac,norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hEn)).mpr
  exact h.trans_eq (by ring)

theorem eventually_uniform_zero_strip (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1/2) :
    ∀ᶠ x : ℝ in atTop, ∀ (t : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x) (w : ℂ)
      (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
      (hp : 100*(t*(‖w‖+1)^3+1) ≤ x) (hs : modelDerivative t w= -(Complex.I*(x : ℂ)))
      (P : ℂ → ℂ) (hP0 : P (x : ℂ)=0)
      (hP : ∀ z ∈ ball (x : ℂ) 1, HasDerivAt P (phaseSlope t x ht hx w hr hi hp hs z) z),
      let a := modelGaussianAmplitude t (x : ℂ) (branch t x ht hx w hr hi hp hs (x : ℂ))
      ∀ z : ℂ, ‖z-(x : ℂ)‖ < 1 → RiemannQuarticFlow.flow t z=0 →
        |(phase a P z).im| ≤ 2*ε ∧ |z.im| ≤ 4*ε/w.re := by
  filter_upwards [eventually_uniform_normalized_cosine_error ε hε] with x he
  intro t ht hx w hr hi hp hs P hP0 hP
  dsimp only
  intro z hz hzero
  let a := modelGaussianAmplitude t (x : ℂ) (branch t x ht hx w hr hi hp hs (x : ℂ))
  have h := he t ht hx w hr hi hp hs P hP0 hP z hz
  rw [hzero,zero_div,zero_sub,norm_neg] at h
  have him := RiemannQuarticZeroStrip.small_cos_im (phase a P z) ε hε.le hεhalf h
  have hlow := phase_im_lower_bound t x ht hx w hr hi hp hs P hP0 hP z hz
  refine ⟨him,?_⟩
  apply (le_div_iff₀ (by linarith : 0 < w.re)).mpr
  nlinarith

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarCosinePhase
