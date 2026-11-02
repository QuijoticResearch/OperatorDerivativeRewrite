import Foundation.StochasticCauchyDiskDerivative
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.ContinuousMap.Compact
noncomputable section
open MeasureTheory Set Filter Metric
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyResolventChronological

open InfiniteGaussian GaussianTimeProcess GaussianBrownianQuadraticVariation StochasticCauchyParameterizedObstruction
open StochasticCauchyJointPastIntegral StochasticCauchyComplexChannels StochasticCauchyPhysicalInput
open StochasticCauchyExponentialInput StochasticCauchyExitClock StochasticCauchyBrownianRealization
open StochasticCauchyStoppedIndicators StochasticCauchyDiskDerivative
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev α : ℂ := ((Real.sqrt 2:ℝ):ℂ)
private abbrev clock (R : ℝ) (T : ℝ≥0) := clippedClock T (exitTime R)
private theorem clock_stopping (R : ℝ) (T : ℝ≥0) :
    IsStoppingTime StochasticCauchyStoppedDomains.augmentedJoint (fun w => (clock R T w:WithTop ℝ≥0)) :=
  clippedClock_stopping T (exitTime R) (exitTime_stopping R)

private def raw (T : ℝ≥0) (u : ComplexInput T) (r : ℝ) (w : Sample) : ℂ :=
  (fieldEmbedding T (realInput T u) ((r,w.1),w.2):ℂ)+
    Complex.I*(fieldEmbedding T (imagInput T u) ((r,w.1),w.2):ℂ)

private theorem real_field_ext (T : ℝ≥0) (u v : Input T)
    (h : ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,fieldEmbedding T u ((r,w.1),w.2)=fieldEmbedding T v ((r,w.1),w.2)) : u=v := by
  apply (fieldEmbedding T).injective
  apply (timeSections T).injective
  apply Lp.ext
  filter_upwards [timeSections_ae T (fieldEmbedding T u),timeSections_ae T (fieldEmbedding T v),h] with r hu hv hh
  apply Lp.ext
  filter_upwards [hu,hv,hh] with w hu hv hh
  exact hu.trans (hh.trans hv.symm)

private theorem input_ext (T : ℝ≥0) (u v : ComplexInput T)
    (h : ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,raw T u r w=raw T v r w) : u=v := by
  have hr : realInput T u=realInput T v := by
    apply real_field_ext T
    filter_upwards [h] with r hh
    filter_upwards [hh] with w hh
    simpa [raw] using congrArg Complex.re hh
  have hi : imagInput T u=imagInput T v := by
    apply real_field_ext T
    filter_upwards [h] with r hh
    filter_upwards [hh] with w hh
    simpa [raw] using congrArg Complex.im hh
  have hn := input_norm_sq T (u-v)
  rw [map_sub,map_sub,hr,hi,sub_self,sub_self] at hn
  simp only [norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_add] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

private theorem combined_integral (T : ℝ≥0) (u v : Input T) :
    valueIntegral T u+Complex.I • valueIntegral T v=channel T false (α • combineInput T u v) := by
  change ComplexL2Isometry.combine μ (integralX T u) (integralY T u)+
    Complex.I • ComplexL2Isometry.combine μ (integralX T v) (integralY T v)=_
  rw [StochasticCauchyExponentialReconstruction.normalized_channel_combine]
  simp only [ComplexL2Isometry.combine,map_add,map_sub,smul_add,smul_smul,Complex.I_mul_I,neg_one_smul]
  abel

theorem resolvent_component_extension (a : ℂ) (R : ℝ) (ha : R<‖a‖) (imag : Bool) :
    ∃ φ : ℂ →ᵇ ℝ,∀ z : ℂ,‖z‖≤R → φ z=
      if imag then ((a-z)⁻¹^2).im else ((a-z)⁻¹^2).re := by
  let D : Set ℂ := Metric.closedBall 0 R
  have hne (z : D) : a-(z:ℂ)≠0 := by
    intro he
    have hz : ‖(z:ℂ)‖≤R := by simpa only [D,Metric.mem_closedBall,dist_zero_right] using z.property
    have heq : a=(z:ℂ) := sub_eq_zero.mp he
    rw [heq] at ha
    exact (not_lt_of_ge hz) ha
  have hc : Continuous (fun z : D => (a-(z:ℂ))⁻¹^2) :=
    ((continuous_const.sub continuous_subtype_val).inv₀ hne).pow 2
  let f : C(D,ℝ) := ⟨fun z => if imag then ((a-(z:ℂ))⁻¹^2).im else ((a-(z:ℂ))⁻¹^2).re,by
    cases imag
    · exact Complex.continuous_re.comp hc
    · exact Complex.continuous_im.comp hc⟩
  let b : D →ᵇ ℝ := ContinuousMap.equivBoundedOfCompact D ℝ f
  obtain ⟨φ,_,hφ⟩ := BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed b isClosed_closedBall
  refine ⟨φ,?_⟩
  intro z hz
  have hzD : z∈D := by simpa only [D,Metric.mem_closedBall,dist_zero_right] using hz
  have hh := congrArg (fun g : D →ᵇ ℝ => g ⟨z,hzD⟩) hφ
  exact hh

private theorem combined_physical (a : ℂ) (R : ℝ) (hR : 0≤R) (T : ℝ≥0)
    (φ ψ : ℂ →ᵇ ℝ)
    (hφ : ∀ z : ℂ,‖z‖≤R → φ z=((a-z)⁻¹^2).re)
    (hψ : ∀ z : ℂ,‖z‖≤R → ψ z=((a-z)⁻¹^2).im) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      raw T (combineInput T
        (StochasticCauchyStoppedCoefficients.stoppedInput φ (clock R T) (clock_stopping R T) T)
        (StochasticCauchyStoppedCoefficients.stoppedInput ψ (clock R T) (clock_stopping R T) T)) r w=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => (a-value r.toNNReal w)⁻¹^2) w := by
  simp only [raw,realInput_combine,imagInput_combine]
  filter_upwards [StochasticCauchyStoppedCoefficients.stoppedInput_physical φ (clock R T) (clock_stopping R T) T,
    StochasticCauchyStoppedCoefficients.stoppedInput_physical ψ (clock R T) (clock_stopping R T) T,
    ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr hi hin
  have hrT : r.toNNReal≤T := Real.toNNReal_le_iff_le_coe.mpr hin.2
  filter_upwards [hr,hi,exit_bounded_ae R hR r.toNNReal] with w hr hi hb
  have he : r≤(clock R T w:ℝ) ↔ (r.toNNReal:WithTop ℝ≥0)≤exitTime R w := by
    rw [← Real.toNNReal_le_iff_le_coe]
    change r.toNNReal≤clippedClock T (exitTime R) w ↔ _
    rw [← WithTop.coe_le_coe,clippedClock_coe,le_min_iff]
    simp only [WithTop.coe_le_coe,hrT,and_true]
  have hd (hh : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w) : ‖value r.toNNReal w‖≤R := by
    have hc : clippedClock r.toNNReal (exitTime R) w=r.toNNReal := by
      apply WithTop.coe_injective
      rw [clippedClock_coe,min_eq_right hh]
    simpa only [hc] using hb
  rw [hr,hi]
  by_cases hh : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w
  · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_true]
    rw [hφ _ (hd hh),hψ _ (hd hh)]
    simpa only [mul_comm] using Complex.re_add_im ((a-value r.toNNReal w)⁻¹^2)
  · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_false,
      Complex.ofReal_zero,mul_zero,add_zero]

/-- Actual left sums with rational derivative and the genuine crossing cell. -/
def resolventSum (a : ℂ) (R : ℝ) (T : ℝ≥0) (n : ℕ) (w : Sample) : ℂ :=
  ∑ i : Fin (n+1),if uniformTime T n i.castSucc<clock R T w then
    (a-value (uniformTime T n i.castSucc) w)⁻¹^2 *
      (value (uniformTime T n i.succ) w-value (uniformTime T n i.castSucc) w) else 0

private theorem sum_components (a : ℂ) (R : ℝ) (T : ℝ≥0) (φ ψ : ℂ →ᵇ ℝ)
    (hφ : ∀ z : ℂ,‖z‖≤R → φ z=((a-z)⁻¹^2).re)
    (hψ : ∀ z : ℂ,‖z‖≤R → ψ z=((a-z)⁻¹^2).im) (n : ℕ) (w : Sample) :
    StochasticCauchyStoppedCoefficients.chronologicalSum φ (clock R T) T n w+
      Complex.I*StochasticCauchyStoppedCoefficients.chronologicalSum ψ (clock R T) T n w=resolventSum a R T n w := by
  simp only [StochasticCauchyStoppedCoefficients.chronologicalSum,resolventSum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hh : uniformTime T n i.castSucc<clock R T w
  · simp only [hh,ite_true]
    have he : (uniformTime T n i.castSucc:WithTop ℝ≥0)<exitTime R w := by
      apply lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hh)
      rw [clock,clippedClock_coe]
      exact min_le_left _ _
    have hd := (before_exit R w _ he).le
    rw [hφ _ hd,hψ _ hd]
    have hre := Complex.re_add_im ((a-value (uniformTime T n i.castSucc) w)⁻¹^2)
    calc
      _ = (((a-value (uniformTime T n i.castSucc) w)⁻¹^2).re+
          Complex.I*(((a-value (uniformTime T n i.castSucc) w)⁻¹^2).im:ℂ))*
          (value (uniformTime T n i.succ) w-value (uniformTime T n i.castSucc) w) := by ring
      _ = _ := by rw [mul_comm Complex.I _,hre]
  · simp only [hh,ite_false,mul_zero,add_zero]

/-- Actual rational-derivative chronological sums have genuine sourceL2 domains
and converge in PHYSICAL SOURCE MEAN SQUARE to the stopped centered resolvent. -/
theorem chronological_resolvent (a : ℂ) (R : ℝ) (hR : 0≤R) (ha : R<‖a‖) (T : ℝ≥0) :
    (∀ n : ℕ,MemLp (resolventSum a R T n) 2 μ) ∧
      Tendsto (fun n => ∫ w,‖resolventSum a R T n w-
        ((a-value (clippedClock T (exitTime R) w) w)⁻¹-a⁻¹)‖^2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨φ,hφ⟩ := resolvent_component_extension a R ha false
  obtain ⟨ψ,hψ⟩ := resolvent_component_extension a R ha true
  simp only [Bool.false_eq_true,ite_false] at hφ
  simp only [ite_true] at hψ
  obtain ⟨v,hv,hphysical,_,_⟩ := resolvent_ito a R hR ha T
  let uφ := StochasticCauchyStoppedCoefficients.stoppedInput φ (clock R T) (clock_stopping R T) T
  let uψ := StochasticCauchyStoppedCoefficients.stoppedInput ψ (clock R T) (clock_stopping R T) T
  let u : ComplexInput T := combineInput T uφ uψ
  have huv : u=v := by
    apply input_ext T
    filter_upwards [combined_physical a R hR T φ ψ hφ hψ,hphysical] with r hu hv
    filter_upwards [hu,hv] with w hu hv
    exact hu.trans hv.symm
  let G : ℕ → JointComplex := fun n =>
    valueIntegral T (StochasticCauchyStoppedCoefficients.gridInput φ (clock R T) (clock_stopping R T) T n)+
      Complex.I • valueIntegral T (StochasticCauchyStoppedCoefficients.gridInput ψ (clock R T) (clock_stopping R T) T n)
  have hl : Tendsto G atTop (𝓝 (channel T false (α • v))) := by
    have ht := (StochasticCauchyStoppedCoefficients.chronological_L2_tendsto φ (clock R T) (clock_stopping R T) T).add
      ((StochasticCauchyStoppedCoefficients.chronological_L2_tendsto ψ (clock R T) (clock_stopping R T) T).const_smul Complex.I)
    have he := combined_integral T uφ uψ
    change valueIntegral T uφ+Complex.I • valueIntegral T uψ=channel T false (α • u) at he
    rw [huv] at he
    change Tendsto G atTop (𝓝 (valueIntegral T uφ+Complex.I • valueIntegral T uψ)) at ht
    rw [he] at ht
    exact ht
  have hG (n : ℕ) : G n =ᵐ[μ] resolventSum a R T n := by
    let X := valueIntegral T (StochasticCauchyStoppedCoefficients.gridInput φ (clock R T) (clock_stopping R T) T n)
    let Y := valueIntegral T (StochasticCauchyStoppedCoefficients.gridInput ψ (clock R T) (clock_stopping R T) T n)
    filter_upwards [Lp.coeFn_add X (Complex.I • Y),Lp.coeFn_smul Complex.I Y,
      StochasticCauchyStoppedCoefficients.chronological_actual φ (clock R T) (clock_stopping R T) T n,
      StochasticCauchyStoppedCoefficients.chronological_actual ψ (clock R T) (clock_stopping R T) T n]
      with w hsum hsmul hφn hψn
    change (X+Complex.I • Y) w=_
    rw [hsum]
    simp only [Pi.add_apply,hsmul,Pi.smul_apply,smul_eq_mul]
    change X w+Complex.I*Y w=_
    rw [hφn,hψn]
    exact sum_components a R T φ ψ hφ hψ n w
  refine ⟨fun n => (Lp.memLp (G n)).ae_eq (hG n),?_⟩
  have hn : Tendsto (fun n => ‖G n-channel T false (α • v)‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((hl.sub_const (channel T false (α • v))).norm.pow 2)
  have he (n : ℕ) : ‖G n-channel T false (α • v)‖^2=
      ∫ w,‖resolventSum a R T n w-((a-value (clippedClock T (exitTime R) w) w)⁻¹-a⁻¹)‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (G n) (channel T false (α • v)),hG n,hv] with w hs hsum hval
    change ‖(G n-channel T false (α • v)) w‖^2=_
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hsum,hval]
  simpa only [he] using hn

end OperatorDerivativeRewrite.Foundation.StochasticCauchyResolventChronological
