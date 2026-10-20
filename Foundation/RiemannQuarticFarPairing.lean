import Foundation.RiemannQuarticFarHalfline
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
/-! Actual far-frequency pairing on the real axis. The error is normalized by
  the norm of the nonzero complex saddle amplitude, never by its real part.
  These estimates retain phase cancellation and do not prove global zero control. -/
noncomputable section
open Set Metric Complex MeasureTheory Filter
open scoped Topology ComplexConjugate
namespace OperatorDerivativeRewrite.Foundation.RiemannQuarticFarPairing
open RiemannQuarticFrequencyBranch RiemannQuarticSaddleTheta RiemannQuarticSaddleBranch
open RiemannQuarticNaturalContour RiemannQuarticFarHalfline RiemannQuarticFarGaussianLimit
open RiemannQuarticFarCorrection

def horizontalIntegral (t : ℝ) (z : ℂ) (h : ℝ) : ℂ :=
  ∫ s : ℝ in Ioi 0, saddleWeight t z ((s : ℂ)+(h : ℂ)*Complex.I)

def modelGaussianAmplitude (t : ℝ) (z v : ℂ) : ℂ :=
  saddleWeight t z v*(∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2))

theorem weight_conj (t : ℝ) (z q : ℂ) :
    saddleWeight t (-conj z) (conj q)=conj (saddleWeight t z q) := by
  unfold saddleWeight
  rw [map_mul,← RiemannQuarticKernelReflection.kernel_conj,← Complex.exp_conj]
  congr 2
  simp only [map_add,map_mul,map_pow,Complex.conj_ofReal,Complex.conj_I]
  ring

theorem horizontal_conj (t : ℝ) (z : ℂ) (h : ℝ) :
    horizontalIntegral t (-conj z) (-h)=conj (horizontalIntegral t z h) := by
  unfold horizontalIntegral
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with s
  have hq : (s : ℂ)+((-h : ℝ) : ℂ)*Complex.I=conj ((s : ℂ)+(h : ℂ)*Complex.I) := by
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg]
    ring
  rw [hq,weight_conj]

theorem flow_real_horizontal (t x h : ℝ) (hh : |h| < Real.pi/8) :
    RiemannQuarticFlow.flow t (x : ℂ)=(horizontalIntegral t (x : ℂ) h).re := by
  rw [flow_eq_paired_horizontal t (x : ℂ) h hh]
  have hc := horizontal_conj t (x : ℂ) h
  simp only [Complex.conj_ofReal] at hc
  have hn : (∫ s : ℝ in Ioi 0, saddleWeight t (-(x : ℂ)) ((s : ℂ)-(h : ℂ)*Complex.I))=
      conj (horizontalIntegral t (x : ℂ) h) := by
    simpa only [horizontalIntegral,Complex.ofReal_neg,neg_mul,← sub_eq_add_neg] using hc
  rw [hn]
  exact (Complex.re_eq_add_conj _).symm

theorem real_pair_error (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral t (x : ℂ) h/A-1‖ ≤ η) :
    ‖RiemannQuarticFlow.flow t (x : ℂ)-(A.re : ℂ)‖ ≤ η*‖A‖ := by
  have hid : horizontalIntegral t (x : ℂ) h/A-1=(horizontalIntegral t (x : ℂ) h-A)/A := by field_simp
  rw [hid,norm_div] at he
  have hnum := (div_le_iff₀ (norm_pos_iff.mpr hA)).mp he
  rw [flow_real_horizontal t x h hh,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (horizontalIntegral t (x : ℂ) h-A)).trans hnum

theorem modelGaussianAmplitude_ne_zero (t x : ℝ) (ht : 1 ≤ t) (hx : 10000 ≤ x)
    (w v : ℂ) (hr : 120020 ≤ w.re) (hi : |w.im| ≤ 1/2)
    (hp : 100*(t*(‖w‖+1)^3+1) ≤ x)
    (hs : modelDerivative t w= -(Complex.I*(x : ℂ))) (hv : ‖v-w‖ ≤ 1/x) (z : ℂ) :
    modelGaussianAmplitude t z v ≠ 0 := by
  have hg := gaussian_normalization_lower t x ht hx w v (by linarith) hi hp hs hv
  have hG : (∫ s : ℝ, Complex.exp (deriv (modelDerivative t) v*(s : ℂ)^2/2)) ≠ 0 := by
    intro h
    norm_num [h] at hg
  have hd := corrected_saddle_geometry t x ht hx w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  exact mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) hd.2.2) hG

theorem real_pair_cosine_error (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral t (x : ℂ) h/A-1‖ ≤ η) :
    |(RiemannQuarticFlow.flow t (x : ℂ)).re/‖A‖-Real.cos A.arg| ≤ η := by
  have herr := real_pair_error t x h hh A hA η he
  have hre := (Complex.abs_re_le_norm (RiemannQuarticFlow.flow t (x : ℂ)-(A.re : ℂ))).trans herr
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  rw [Complex.cos_arg hA,← sub_div,abs_div,abs_of_pos (norm_pos_iff.mpr hA)]
  exact (div_le_iff₀ (norm_pos_iff.mpr hA)).mpr hre

theorem real_pair_zero_phase (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral t (x : ℂ) h/A-1‖ ≤ η)
    (hz : RiemannQuarticFlow.flow t (x : ℂ)=0) : |Real.cos A.arg| ≤ η := by
  have h := real_pair_cosine_error t x h hh A hA η he
  simpa only [hz,Complex.zero_re,zero_div,zero_sub,abs_neg] using h

theorem real_pair_nonzero (t x h : ℝ) (hh : |h| < Real.pi/8) (A : ℂ)
    (hA : A ≠ 0) (η : ℝ) (he : ‖horizontalIntegral t (x : ℂ) h/A-1‖ ≤ η)
    (hphase : η < |Real.cos A.arg|) : RiemannQuarticFlow.flow t (x : ℂ) ≠ 0 := by
  intro hz
  exact (not_lt_of_ge (real_pair_zero_phase t x h hh A hA η he hz)) hphase

theorem eventually_uniform_real_flow_error (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∀ t : ℝ, 1 ≤ t → ∀ w v : ℂ,
      120020 ≤ w.re → |w.im| ≤ 1/2 → 100*(t*(‖w‖+1)^3+1) ≤ x →
      modelDerivative t w= -(Complex.I*(x : ℂ)) → ‖v-w‖ ≤ 1/x →
      ∀ y : ℝ, complexSlope t v= -(Complex.I*(y : ℂ)) →
      modelGaussianAmplitude t (y : ℂ) v ≠ 0 ∧
      ‖RiemannQuarticFlow.flow t (y : ℂ)-((modelGaussianAmplitude t (y : ℂ) v).re : ℂ)‖ ≤
        η*‖modelGaussianAmplitude t (y : ℂ) v‖ ∧
      |(RiemannQuarticFlow.flow t (y : ℂ)).re/‖modelGaussianAmplitude t (y : ℂ) v‖-
        Real.cos (modelGaussianAmplitude t (y : ℂ) v).arg| ≤ η := by
  filter_upwards [eventually_uniform_horizontal_gaussian_error η hη,eventually_ge_atTop (10000 : ℝ)]
    with x he hx
  intro t ht w v hr hi hp hs hv y hz
  have hd := corrected_saddle_geometry t x ht hx w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv)
  have hA := modelGaussianAmplitude_ne_zero t x ht hx w v hr hi hp hs hv (y : ℂ)
  have he' := (he t ht w v hr hi hp hs hv (y : ℂ) hz (by simp)).2
  change ‖horizontalIntegral t (y : ℂ) v.im/modelGaussianAmplitude t (y : ℂ) v-1‖ ≤ η at he'
  exact ⟨hA,real_pair_error t y v.im hd.2.1 _ hA η he',
    real_pair_cosine_error t y v.im hd.2.1 _ hA η he'⟩

theorem eventually_actual_real_flow_cosine (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∃ w v : ℂ,
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧ complexSlope t v= -(Complex.I*(x : ℂ)) ∧
      1 ≤ v.re ∧ |v.im| < Real.pi/8 ∧ modelGaussianAmplitude t (x : ℂ) v ≠ 0 ∧
      |(RiemannQuarticFlow.flow t (x : ℂ)).re/‖modelGaussianAmplitude t (x : ℂ) v‖-
        Real.cos (modelGaussianAmplitude t (x : ℂ) v).arg| ≤ η := by
  filter_upwards [eventually_controlled_far_saddles t ht,eventually_uniform_real_flow_error η hη]
    with x hdata he
  obtain ⟨hx,w,v,hr,hi,hp,hs,hv,hz,hvre,hvim,hkn⟩ := hdata
  have h := he t ht w v hr hi hp hs hv x hz
  exact ⟨w,v,hs,hz,hvre,hvim,h.1,h.2.2⟩

theorem real_flow_cosine_limit_for_saddle_family (t : ℝ) (ht : 1 ≤ t) (w v : ℝ → ℂ)
    (hdata : ∀ᶠ x : ℝ in atTop, 120020 ≤ (w x).re ∧ |(w x).im| ≤ 1/2 ∧
      100*(t*(‖w x‖+1)^3+1) ≤ x ∧ modelDerivative t (w x)= -(Complex.I*(x : ℂ)) ∧
      ‖v x-w x‖ ≤ 1/x ∧ complexSlope t (v x)= -(Complex.I*(x : ℂ))) :
    Tendsto (fun x : ℝ => (RiemannQuarticFlow.flow t (x : ℂ)).re/
      ‖modelGaussianAmplitude t (x : ℂ) (v x)‖-
      Real.cos (modelGaussianAmplitude t (x : ℂ) (v x)).arg) atTop (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  filter_upwards [eventually_uniform_real_flow_error (η/2) (by positivity),hdata]
    with x he hd
  obtain ⟨hr,hi,hp,hs,hv,hz⟩ := hd
  have h := (he t ht (w x) (v x) hr hi hp hs hv x hz).2.2
  have hlt := lt_of_le_of_lt h (by linarith : η/2 < η)
  simpa only [Real.dist_eq,sub_zero] using hlt

theorem eventually_real_disk_flow_cosine (t : ℝ) (ht : 1 ≤ t) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ x : ℝ in atTop, ∃ w : ℂ,
      modelDerivative t w= -(Complex.I*(x : ℂ)) ∧
      ∀ y : ℝ, |y-x| ≤ 1 → ∃! v : ℂ,
        v ∈ closedBall w (1/x) ∧ complexSlope t v= -(Complex.I*(y : ℂ)) ∧
        modelGaussianAmplitude t (y : ℂ) v ≠ 0 ∧
        |(RiemannQuarticFlow.flow t (y : ℂ)).re/‖modelGaussianAmplitude t (y : ℂ) v‖-
          Real.cos (modelGaussianAmplitude t (y : ℂ) v).arg| ≤ η := by
  filter_upwards [eventually_controlled_far_saddles t ht,eventually_uniform_real_flow_error η hη]
    with x hdata he
  obtain ⟨hx,w,v₀,hr,hi,hp,hs,hv₀,hz₀,hvre,hvim,hkn⟩ := hdata
  refine ⟨w,hs,?_⟩
  intro y hy
  have hy' : ‖(y : ℂ)-(x : ℂ)‖ ≤ 1 := by
    simpa only [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hy
  obtain ⟨v,hv,huniq⟩ := actual_far_frequency_disk t x ht hx w hr hi hp hs (y : ℂ) hy'
  have h := he t ht w v hr hi hp hs
    (by simpa only [mem_closedBall,dist_eq_norm] using hv.1) y hv.2
  refine ⟨v,⟨hv.1,hv.2,h.1,h.2.2⟩,?_⟩
  intro q hq
  exact huniq q ⟨hq.1,hq.2.1⟩

end OperatorDerivativeRewrite.Foundation.RiemannQuarticFarPairing
