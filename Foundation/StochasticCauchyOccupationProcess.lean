import Foundation.StochasticCauchyOccupationEnergy
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyOccupationProcess
open InfiniteGaussian StochasticCauchyExitClock StochasticCauchyStoppedDomains
open StochasticCauchyBrownianRealization
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct

/-- Continuous physical speed along the actual two-source Brownian path. -/
def rate (g : ℂ → ℂ) (w : Sample) (r : ℝ) : ℝ := ‖g (value r.toNNReal w)‖^2

/-- Unstopped primitive; stopping is introduced explicitly below. -/
def primitive (g : ℂ → ℂ) (T : ℝ≥0) (w : Sample) : ℝ :=
  ∫ r in 0..(T:ℝ), rate g w r

theorem rate_continuous (g : ℂ → ℂ) (hg : Continuous g) (w : Sample) :
    Continuous (rate g w) :=
  ((hg.comp ((value_continuous w).comp continuous_real_toNNReal)).norm).pow 2

theorem primitive_continuous (g : ℂ → ℂ) (hg : Continuous g) (w : Sample) :
    Continuous (fun T => primitive g T w) := by
  have hc := rate_continuous g hg w
  have hp : Continuous (fun t : ℝ => ∫ r in 0..t, rate g w r) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt
  exact hp.comp NNReal.continuous_coe

theorem primitive_monotone (g : ℂ → ℂ) (hg : Continuous g) (w : Sample) :
    Monotone (fun T => primitive g T w) := by
  intro s t hst
  apply intervalIntegral.integral_mono_interval (le_refl (0:ℝ)) s.coe_nonneg
    (show (s:ℝ)≤t from hst)
  · exact Eventually.of_forall (fun r => sq_nonneg _)
  · exact (rate_continuous g hg w).intervalIntegrable 0 t

theorem primitive_adapted (g : ℂ → ℂ) (hg : Continuous g) :
    StronglyAdapted augmentedJoint (primitive g) := by
  intro T
  let : MeasurableSpace Sample := augmentedJoint T
  have hv : Measurable (fun q : ℝ × Sample => value (min T q.1.toNNReal) q.2) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun w => (value_continuous w).comp (continuous_const.min continuous_real_toNNReal))
      (fun r : ℝ => ((continuous_stronglyAdapted (min T r.toNNReal)).mono
        (augmentedJoint.mono (min_le_left T r.toNNReal))).measurable)
  have hm : Measurable (fun q : ℝ × Sample => ‖g (value (min T q.1.toNNReal) q.2)‖^2) :=
    (hg.measurable.comp hv).norm.pow_const 2
  have hi := (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'
    (ν := StochasticCauchyExponentialInput.timeLaw T)
  convert hi using 1
  funext w
  rw [primitive, intervalIntegral.integral_of_le T.coe_nonneg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  have hnn : r.toNNReal≤T := by
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ hr.1.le]
    exact hr.2
  change rate g w r = ‖g (value (min T r.toNNReal) w)‖^2
  simp only [min_eq_right hnn,rate]


/-- The physical survival integral is exactly a stopped continuous primitive. -/
theorem clock_eq_stopped (g : ℂ → ℂ) (R : ℝ) (T : ℝ≥0) (w : Sample) :
    StochasticCauchyOccupationEnergy.clock g R T w =
      primitive g (clippedClock T (exitTime R) w) w := by
  cases hw : exitTime R w with
  | top =>
    simp only [clippedClock,hw,min_eq_right le_top,WithTop.untopD_coe]
    rw [primitive,intervalIntegral.integral_of_le T.coe_nonneg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun r => by
      have hs : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w := by rw [hw];exact le_top
      exact Set.indicator_of_mem
        (s := {q : ℝ × Sample | (q.1.toNNReal:WithTop ℝ≥0)≤exitTime R q.2})
        (a := (r,w)) hs (fun q : ℝ × Sample => ‖g (value q.1.toNNReal q.2)‖^2))
  | coe u =>
    have hd : (fun r => StochasticCauchyOccupationEnergy.density g R (r,w)) =
        (Iic (u:ℝ)).indicator (rate g w) := by
      funext r
      have hi : r.toNNReal≤u ↔ r≤(u:ℝ) := by
        simpa only [Real.toNNReal_coe] using (Real.toNNReal_le_toNNReal_iff (r := r) u.coe_nonneg)
      simp only [StochasticCauchyOccupationEnergy.density,Set.indicator,Set.mem_ofPred_eq,
        hw,WithTop.coe_le_coe,hi,mem_Iic,rate]
    change (∫ r in Ioc 0 (T:ℝ), StochasticCauchyOccupationEnergy.density g R (r,w)) = _
    rw [hd,setIntegral_indicator measurableSet_Iic,Ioc_inter_Iic]
    simp only [clippedClock,hw,← WithTop.coe_min,WithTop.untopD_coe,primitive]
    rw [intervalIntegral.integral_of_le (min u T).coe_nonneg,NNReal.coe_min,min_comm]

private theorem clipped_continuous (τ : Sample → WithTop ℝ≥0) (w : Sample) :
    Continuous (fun T => clippedClock T τ w) := by
  cases hw : τ w with
  | top =>
    simp only [clippedClock,hw,min_eq_right le_top,WithTop.untopD_coe]
    exact continuous_id
  | coe u =>
    simpa only [clippedClock,hw,← WithTop.coe_min,WithTop.untopD_coe] using
      (continuous_const.min continuous_id : Continuous (fun t : ℝ≥0 => min u t))

private theorem clipped_adapted (M : ℝ≥0 → Sample → ℝ)
    (ha : StronglyAdapted augmentedJoint M) (hc : ∀ w, Continuous (fun t => M t w))
    (τ : Sample → WithTop ℝ≥0) (hτ : IsStoppingTime augmentedJoint τ) :
    StronglyAdapted augmentedJoint (fun t w => M (clippedClock t τ w) w) := by
  intro t
  have h := (ha.stoppedProcess hc hτ) t
  convert h using 1
  funext w
  cases hw : τ w with
  | top =>
    change M (WithTop.untopD 0 (min (τ w) t)) w=M (min (t:WithTop ℝ≥0) (τ w)).untopA w
    rw [hw,min_eq_right le_top,min_eq_left le_top]
    rfl
  | coe u =>
    change M (WithTop.untopD 0 (min (τ w) t)) w=M (min (t:WithTop ℝ≥0) (τ w)).untopA w
    rw [hw,← WithTop.coe_min,← WithTop.coe_min,min_comm]
    rfl

theorem clock_continuous (g : ℂ → ℂ) (hg : Continuous g) (R : ℝ) (w : Sample) :
    Continuous (fun T => StochasticCauchyOccupationEnergy.clock g R T w) := by
  simp_rw [clock_eq_stopped]
  exact (primitive_continuous g hg w).comp (clipped_continuous (exitTime R) w)

theorem clock_monotone (g : ℂ → ℂ) (hg : Continuous g) (R : ℝ) (w : Sample) :
    Monotone (fun T => StochasticCauchyOccupationEnergy.clock g R T w) := by
  intro s t hst
  simp_rw [clock_eq_stopped]
  apply primitive_monotone g hg w
  apply WithTop.coe_le_coe.mp
  rw [clippedClock_coe,clippedClock_coe]
  exact min_le_min_left _ (WithTop.coe_le_coe.mpr hst)

theorem clock_adapted (g : ℂ → ℂ) (hg : Continuous g) (R : ℝ) :
    StronglyAdapted augmentedJoint (fun T w => StochasticCauchyOccupationEnergy.clock g R T w) := by
  simp_rw [clock_eq_stopped]
  exact clipped_adapted (primitive g) (primitive_adapted g hg) (primitive_continuous g hg)
    (exitTime R) (exitTime_stopping R)

/-- A single continuous adapted version agrees with the local analytic clock
at EVERY horizon on ONE probability-one source event. -/
theorem analytic_clock_version (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    ∃ A : ℝ≥0 → Sample → ℝ, StronglyAdapted augmentedJoint A ∧
      (∀ w, Continuous (fun T => A T w)) ∧ (∀ w, Monotone (fun T => A T w)) ∧
      (∀ T w, 0≤A T w) ∧
      (∀ᵐ w ∂μ, ∀ T, A T w=StochasticCauchyOccupationEnergy.clock (deriv f) R T w) := by
  obtain ⟨g,hg⟩ := StochasticCauchyAnalyticMartingale.continuous_extension
    (deriv f) R S hRS (hf.deriv Metric.isOpen_ball)
  refine ⟨fun T w => StochasticCauchyOccupationEnergy.clock g R T w,
    clock_adapted g g.continuous R,clock_continuous g g.continuous R,
    clock_monotone g g.continuous R,
    (fun T w => StochasticCauchyOccupationEnergy.clock_nonneg g R T w),?_⟩
  filter_upwards [value_zero_ae] with w hw
  intro T
  apply integral_congr_ae
  apply Eventually.of_forall
  intro r
  by_cases hs : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w
  · have hc : clippedClock r.toNNReal (exitTime R) w=r.toNNReal := by
      apply WithTop.coe_injective
      rw [clippedClock_coe,min_eq_right hs]
    have hb := exit_stopped_bound (R:ℝ) r.toNNReal w (by rw [hw,norm_zero];exact R.coe_nonneg)
    rw [hc] at hb
    simp only [StochasticCauchyOccupationEnergy.density,Set.indicator,Set.mem_ofPred_eq,hs,ite_true]
    rw [hg _ hb]
  · simp only [StochasticCauchyOccupationEnergy.density,Set.indicator,Set.mem_ofPred_eq,hs,ite_false]


/-- The physical clock is killed at exit; it is not globally invertible. -/
theorem clock_flat_after_exit (g : ℂ → ℂ) (R : ℝ) (s t : ℝ≥0) (w : Sample)
    (hs : exitTime R w≤(s:WithTop ℝ≥0)) (ht : exitTime R w≤(t:WithTop ℝ≥0)) :
    StochasticCauchyOccupationEnergy.clock g R s w=StochasticCauchyOccupationEnergy.clock g R t w := by
  simp only [clock_eq_stopped,clippedClock,min_eq_left hs,min_eq_left ht]

/-- Unit speed recovers the actual clipped exit duration, sample by sample. -/
theorem clock_one (R : ℝ) (T : ℝ≥0) (w : Sample) :
    StochasticCauchyOccupationEnergy.clock (fun _ => (1:ℂ)) R T w=
      (clippedClock T (exitTime R) w:ℝ) := by
  simp [clock_eq_stopped,primitive,rate]

/-- Even without global regularity of f, its original physical clock has
continuous nondecreasing paths on one common probability-one source event. -/
theorem analytic_clock_paths (f : ℂ → ℂ) (R S : ℝ≥0) (hRS : R<S)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 S)) :
    ∀ᵐ w ∂μ, Continuous (fun T => StochasticCauchyOccupationEnergy.clock (deriv f) R T w) ∧
      Monotone (fun T => StochasticCauchyOccupationEnergy.clock (deriv f) R T w) := by
  obtain ⟨A,ha,hc,hm,hn,he⟩ := analytic_clock_version f R S hRS hf
  filter_upwards [he] with w hw
  have hfun : (fun T => A T w)=(fun T => StochasticCauchyOccupationEnergy.clock (deriv f) R T w) := funext hw
  exact ⟨hfun ▸ hc w,hfun ▸ hm w⟩

end OperatorDerivativeRewrite.Foundation.StochasticCauchyOccupationProcess
