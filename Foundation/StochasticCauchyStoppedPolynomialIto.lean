import Foundation.StochasticCauchyStoppedErrors

/-! Actual stopped polynomial Ito identity in the original complex native domain. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedPolynomialIto
open InfiniteGaussian ComplexL2Isometry GaussianBrownianQuadraticVariation
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
open StochasticCauchyStoppedDomains StochasticCauchyExitClock StochasticCauchyStoppedErrors
open StochasticCauchyBrownianRealization
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyComplexChannels.complexInput_complete
  StochasticCauchyParameterizedObstruction.predictableTime
private abbrev Sample := SampleSpace × SampleSpace
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev valueIntegral := StochasticCauchyStoppedIndicators.valueIntegral
private abbrev W := StochasticCauchyStoppedCoefficients.stoppedInput
private abbrev G := StochasticCauchyStoppedCoefficients.gridInput

private def pathSum {m : ℕ} (t : Fin (m+1) → ℝ≥0) (c : ℝ≥0) (v : ℝ≥0 → ℂ) : ℂ :=
  ∑ i : Fin m,if t i.castSucc<c then v (t i.succ)-v (t i.castSucc) else 0

private theorem pathSum_cell {m : ℕ} (t : Fin (m+1) → ℝ≥0) (ht : Monotone t)
    (c : ℝ≥0) (v : ℝ≥0 → ℂ) (i : Fin m) (hi : t i.castSucc<c ∧ c≤t i.succ) :
    pathSum t c v=v (t i.succ)-v (t 0) := by
  have he (j : Fin m) : t j.castSucc<c ↔ j≤ i := by
    constructor
    · intro hj
      by_contra hji
      have hle := ht (Fin.succ_le_castSucc_iff.mpr (lt_of_not_ge hji))
      exact (not_lt_of_ge (hi.2.trans hle)) hj
    · intro hj;exact (ht (Fin.castSucc_le_castSucc_iff.mpr hj)).trans_lt hi.1
  simp only [pathSum,he]
  rw [← Finset.sum_filter]
  have hs : Finset.univ.filter (fun j : Fin m => j≤ i)=Finset.Iic i := by ext j;simp
  rw [hs]
  exact Fin.sum_Iic_sub i (fun j => v (t j))

private theorem pathSum_all (T : ℝ≥0) (n : ℕ) (c : ℝ≥0) (hc : T<c) (v : ℝ≥0 → ℂ) :
    pathSum (uniformTime T n) c v=v T-v 0 := by
  have he (i : Fin (n+1)) : uniformTime T n i.castSucc<c := by
    have hle : uniformTime T n i.castSucc≤T := by
      simpa only [(uniformTime_endpoints T n).2] using
        uniformTime_monotone T n (Fin.le_last i.castSucc)
    exact hle.trans_lt hc
  simp only [pathSum,he,ite_true]
  have hsum := Fin.sum_Iic_sub (Fin.last n) (fun j => v (uniformTime T n j))
  have hh : Finset.Iic (Fin.last n)=Finset.univ := by
    ext j;simp only [Finset.mem_Iic,Finset.mem_univ,iff_true];exact Fin.le_last _
  rw [hh,show (Fin.last n).succ=Fin.last (n+1) from rfl] at hsum
  simpa only [(uniformTime_endpoints T n).1,(uniformTime_endpoints T n).2] using hsum

/-- Pathwise convergence of actual stopped increment sums; no L2 bound on
sampled Brownian values is assumed. -/
private theorem pathSum_tendsto (T : ℝ≥0) (c : ℝ≥0) (v : ℝ≥0 → ℂ) (hv : Continuous v) :
    Tendsto (fun n => pathSum (uniformTime T n) c v) atTop (𝓝 (v (min T c)-v 0)) := by
  by_cases hc : c=0
  · subst c
    simp only [pathSum,not_lt_zero,ite_false,Finset.sum_const_zero,min_zero,sub_self]
    exact tendsto_const_nhds
  by_cases hcT : c≤T
  · have hp : 0<(c:ℝ) := by exact_mod_cast (lt_of_le_of_ne bot_le (Ne.symm hc))
    choose i hi using fun n => GaussianQuadraticIto.uniformTime_covers T n c ⟨hp,hcT⟩
    have hn (n : ℕ) : ‖(uniformTime T n (i n).succ:ℝ)-(c:ℝ)‖≤(T:ℝ)/(n+1) := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hi n).2)]
      have hs := uniformTime_step T n (i n)
      linarith [(hi n).1]
    have hz : Tendsto (fun n : ℕ => (T:ℝ)/(n+1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have hr := tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hn hz)
    have hnn := continuous_real_toNNReal.continuousAt.tendsto.comp hr
    simp only [Function.comp_def,Real.toNNReal_coe] at hnn
    have hvv := (hv.continuousAt.tendsto.comp hnn).sub_const (v 0)
    rw [min_eq_right hcT]
    convert hvv using 1
    funext n
    have hcell : uniformTime T n (i n).castSucc<c ∧ c≤uniformTime T n (i n).succ :=
      ⟨(hi n).1,(hi n).2⟩
    simpa only [(uniformTime_endpoints T n).1,Function.comp_apply] using
      pathSum_cell (uniformTime T n) (uniformTime_monotone T n) c v (i n) hcell
  · have hTc := lt_of_not_ge hcT
    simp only [pathSum_all T _ c hTc v,min_eq_left hTc.le]
    exact tendsto_const_nhds

private theorem combineInput_tendsto (T : ℝ≥0) (a b : ℕ → Input T) (u v : Input T)
    (ha : Tendsto a atTop (𝓝 u)) (hb : Tendsto b atTop (𝓝 v)) :
    Tendsto (fun N => combineInput T (a N) (b N)) atTop (𝓝 (combineInput T u v)) := by
  apply tendsto_subtype_rng.mpr
  have har := (continuous_subtype_val.tendsto u).comp ha
  have hbr := (continuous_subtype_val.tendsto v).comp hb
  change Tendsto (fun N => ofReal (nativeMeasure T) (a N).val+
      Complex.I • ofReal (nativeMeasure T) (b N).val) atTop
    (𝓝 (ofReal (nativeMeasure T) u.val+Complex.I • ofReal (nativeMeasure T) v.val))
  exact (((ofReal (nativeMeasure T)).continuous.tendsto _).comp har).add
    (tendsto_const_nhds.smul (((ofReal (nativeMeasure T)).continuous.tendsto _).comp hbr))

private theorem channel_pair (T : ℝ≥0) (a b : Input T) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • combineInput T a b)=valueIntegral T a+Complex.I • valueIntegral T b := by
  rw [StochasticCauchyExponentialReconstruction.normalized_channel_combine]
  apply Lp.ext
  filter_upwards [combine_ae μ (integralX T a-integralY T b) (integralX T b+integralY T a),
    Lp.coeFn_sub (integralX T a) (integralY T b),Lp.coeFn_add (integralX T b) (integralY T a),
    combine_ae μ (integralX T a) (integralY T a),combine_ae μ (integralX T b) (integralY T b),
    Lp.coeFn_add (valueIntegral T a) (Complex.I • valueIntegral T b),
    Lp.coeFn_smul Complex.I (valueIntegral T b)] with w h1 h2 h3 h4 h5 h6 h7
  change valueIntegral T a w=_ at h4
  change valueIntegral T b w=_ at h5
  simp only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h2 h3 h6 h7
  rw [h1,h6,h7,h4,h5,h2,h3,Complex.ofReal_sub,Complex.ofReal_add]
  apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im] <;> ring

variable (φ ψ : ℂ →ᵇ ℝ) (τ : Sample → ℝ≥0)
  (hτ : IsStoppingTime augmentedJoint (fun w => (τ w:WithTop ℝ≥0)))

def derivativeInput (T : ℝ≥0) : ComplexInput T := combineInput T (W φ τ hτ T) (W ψ τ hτ T)
def derivativeGrid (T : ℝ≥0) (n : ℕ) : ComplexInput T := combineInput T (G φ τ hτ T n) (G ψ τ hτ T n)

theorem derivativeGrid_tendsto (T : ℝ≥0) :
    Tendsto (derivativeGrid φ ψ τ hτ T) atTop (𝓝 (derivativeInput φ ψ τ hτ T)) :=
  combineInput_tendsto T _ _ _ _ (StochasticCauchyStoppedCoefficients.gridInput_tendsto φ τ hτ T)
    (StochasticCauchyStoppedCoefficients.gridInput_tendsto ψ τ hτ T)

def derivativeSum (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) (w : Sample) : ℂ :=
  ∑ i : Fin (n+1),if uniformTime T n i.castSucc<τ w then
    p.derivative.eval (value (uniformTime T n i.castSucc) w)*
      (value (uniformTime T n i.succ) w-value (uniformTime T n i.castSucc) w) else 0

private theorem component_sums (T : ℝ≥0) (p : Polynomial ℂ) (R : ℝ)
    (hφ : ∀ z : ℂ,‖z‖≤R → φ z=(p.derivative.eval z).re)
    (hψ : ∀ z : ℂ,‖z‖≤R → ψ z=(p.derivative.eval z).im)
    (hbefore : ∀ s w,s<τ w → ‖value s w‖≤R) (n : ℕ) (w : Sample) :
    StochasticCauchyStoppedCoefficients.chronologicalSum φ τ T n w+
      Complex.I*StochasticCauchyStoppedCoefficients.chronologicalSum ψ τ T n w=derivativeSum τ T p n w := by
  simp only [StochasticCauchyStoppedCoefficients.chronologicalSum,derivativeSum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hh : uniformTime T n i.castSucc<τ w
  · simp only [hh,ite_true]
    rw [hφ _ (hbefore _ _ hh),hψ _ (hbefore _ _ hh)]
    have hz : ((p.derivative.eval (value (uniformTime T n i.castSucc) w)).re:ℂ)+
        Complex.I*((p.derivative.eval (value (uniformTime T n i.castSucc) w)).im:ℂ)=
        p.derivative.eval (value (uniformTime T n i.castSucc) w) := by
      simpa only [mul_comm] using Complex.re_add_im (p.derivative.eval (value (uniformTime T n i.castSucc) w))
    calc
      _ = (((p.derivative.eval (value (uniformTime T n i.castSucc) w)).re:ℂ)+
        Complex.I*((p.derivative.eval (value (uniformTime T n i.castSucc) w)).im:ℂ))*
        (value (uniformTime T n i.succ) w-value (uniformTime T n i.castSucc) w) := by ring
      _ = _ := by rw [hz]
  · simp only [hh,ite_false,mul_zero,add_zero]

private theorem derivativeGrid_actual (T : ℝ≥0) (p : Polynomial ℂ) (R : ℝ)
    (hφ : ∀ z : ℂ,‖z‖≤R → φ z=(p.derivative.eval z).re)
    (hψ : ∀ z : ℂ,‖z‖≤R → ψ z=(p.derivative.eval z).im)
    (hbefore : ∀ s w,s<τ w → ‖value s w‖≤R) (n : ℕ) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid φ ψ τ hτ T n) =ᵐ[μ] derivativeSum τ T p n := by
  rw [derivativeGrid,channel_pair]
  filter_upwards [Lp.coeFn_add (valueIntegral T (G φ τ hτ T n)) (Complex.I • valueIntegral T (G ψ τ hτ T n)),
    Lp.coeFn_smul Complex.I (valueIntegral T (G ψ τ hτ T n)),
    StochasticCauchyStoppedCoefficients.chronological_actual φ τ hτ T n,
    StochasticCauchyStoppedCoefficients.chronological_actual ψ τ hτ T n] with w h1 h2 h3 h4
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at h1 h2
  change valueIntegral T (G φ τ hτ T n) w=_ at h3
  change valueIntegral T (G ψ τ hτ T n) w=_ at h4
  rw [h1,h2,h3,h4]
  exact component_sums φ ψ τ T p R hφ hψ hbefore n w

private def reconstructionGrid (T : ℝ≥0) (p : Polynomial ℂ) (n : ℕ) : JointComplex :=
  channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid φ ψ τ hτ T n)+stoppedErrorSum τ hτ T p n

private theorem reconstructionGrid_tendsto (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (reconstructionGrid φ ψ τ hτ T p) atTop
      (𝓝 (channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeInput φ ψ τ hτ T))) := by
  have hi : Tendsto (fun n => channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid φ ψ τ hτ T n)) atTop
      (𝓝 (channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeInput φ ψ τ hτ T))) :=
    ((channel T false).continuous.tendsto _).comp
      (tendsto_const_nhds.smul (derivativeGrid_tendsto φ ψ τ hτ T))
  have hn : Tendsto (fun n => ‖stoppedErrorSum τ hτ T p n‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp (stopped_error_norm_sq_tendsto τ hτ T p)
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using h
  have he : Tendsto (stoppedErrorSum τ hτ T p) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero] using hn)
  change Tendsto (fun n => channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid φ ψ τ hτ T n)+
    stoppedErrorSum τ hτ T p n) atTop (𝓝 (channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeInput φ ψ τ hτ T)))
  simpa only [add_zero] using hi.add he

private theorem reconstructionGrid_actual (T : ℝ≥0) (p : Polynomial ℂ) (R : ℝ)
    (hφ : ∀ z : ℂ,‖z‖≤R → φ z=(p.derivative.eval z).re)
    (hψ : ∀ z : ℂ,‖z‖≤R → ψ z=(p.derivative.eval z).im)
    (hbefore : ∀ s w,s<τ w → ‖value s w‖≤R) (n : ℕ) :
    reconstructionGrid φ ψ τ hτ T p n =ᵐ[μ] fun w =>
      pathSum (uniformTime T n) (τ w) (fun t => p.eval (value t w)) := by
  filter_upwards [Lp.coeFn_add (channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid φ ψ τ hτ T n))
      (stoppedErrorSum τ hτ T p n),
    derivativeGrid_actual φ ψ τ hτ T p R hφ hψ hbefore n,stoppedErrorSum_actual τ hτ T p n]
    with w h1 h2 h3
  change reconstructionGrid φ ψ τ hτ T p n w=
    channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid φ ψ τ hτ T n) w+stoppedErrorSum τ hτ T p n w at h1
  rw [h1,h2,h3]
  simp only [derivativeSum,chronologicalRemainder,pathSum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hh : uniformTime T n i.castSucc<τ w <;> simp only [hh,ite_true,ite_false] <;> ring

/-- Actual stopped polynomial identity for bounded derivative extensions.
Every approximation and native-domain hypothesis is explicit. -/
theorem bounded_extension_ito (T : ℝ≥0) (p : Polynomial ℂ) (R : ℝ)
    (hφ : ∀ z : ℂ,‖z‖≤R → φ z=(p.derivative.eval z).re)
    (hψ : ∀ z : ℂ,‖z‖≤R → ψ z=(p.derivative.eval z).im)
    (hbefore : ∀ s w,s<τ w → ‖value s w‖≤R) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeInput φ ψ τ hτ T) =ᵐ[μ] fun w =>
      p.eval (value (min T (τ w)) w)-p.eval 0 := by
  have hl := reconstructionGrid_tendsto φ ψ τ hτ T p
  obtain ⟨ns,hns,hn⟩ := (tendstoInMeasure_of_tendsto_Lp hl).exists_seq_tendsto_ae
  filter_upwards [hn,ae_all_iff.mpr (fun n => reconstructionGrid_actual φ ψ τ hτ T p R hφ hψ hbefore n),value_zero_ae]
    with w hn hall h0
  have hp : Continuous (fun t => p.eval (value t w)) := by
    have hh : Continuous (fun z : ℂ => p.eval z) := by fun_prop
    exact hh.comp (value_continuous w)
  have hlim := (pathSum_tendsto T (τ w) _ hp).comp hns.tendsto_atTop
  simp only [hall] at hn
  rw [h0] at hlim
  exact tendsto_nhds_unique hn hlim

private def extension (p : Polynomial ℂ) (R : ℝ) (imag : Bool) : ℂ →ᵇ ℝ :=
  Classical.choose (StochasticCauchyStoppedCoefficients.derivative_component_extension p R imag)

private theorem extension_agrees (p : Polynomial ℂ) (R : ℝ) (imag : Bool) :
    ∀ z : ℂ,‖z‖≤R → extension p R imag z=
      if imag then (p.derivative.eval z).im else (p.derivative.eval z).re :=
  Classical.choose_spec (StochasticCauchyStoppedCoefficients.derivative_component_extension p R imag)

/-- Actual unnormalized polynomial derivative input, stopped at the true radial
exit with the original possibly infinite clock clipped atT. -/
def exitDerivativeInput (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) : ComplexInput T :=
  derivativeInput (extension p R false) (extension p R true)
    (clippedClock T (exitTime R)) (clippedClock_stopping T _ (exitTime_stopping R)) T

/-- Genuine stopped polynomial Ito identity on the ORIGINAL stochastic channel.
The physical integrator is dZ; the existing channel is dZ/sqrt2. -/
theorem exit_polynomial_ito (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R T) =ᵐ[μ] fun w =>
      p.eval (value (clippedClock T (exitTime R) w) w)-p.eval 0 := by
  have hφ : ∀ z : ℂ,‖z‖≤R → extension p R false z=(p.derivative.eval z).re := extension_agrees p R false
  have hψ : ∀ z : ℂ,‖z‖≤R → extension p R true z=(p.derivative.eval z).im := extension_agrees p R true
  have hbefore : ∀ s w,s<clippedClock T (exitTime R) w → ‖value s w‖≤R := by
    intro s w hs
    have hc : (s:WithTop ℝ≥0)<exitTime R w := (WithTop.coe_lt_coe.mpr hs).trans_le (by
      rw [clippedClock_coe]
      exact min_le_left _ _)
    exact (before_exit R w s hc).le
  have hi := bounded_extension_ito (extension p R false) (extension p R true)
    (clippedClock T (exitTime R)) (clippedClock_stopping T _ (exitTime_stopping R)) T p R hφ hψ hbefore
  have hm (w : Sample) : min T (clippedClock T (exitTime R) w)=clippedClock T (exitTime R) w :=
    min_eq_right (clippedClock_le T _ w)
  simpa only [hm,exitDerivativeInput] using hi

/-- Exact actual derivative field of the SAME input appearing in the Ito identity.
No flat Gaussian derivative of the stopped terminal value is assumed. -/
theorem exitDerivativeInput_physical (p : Polynomial ℂ) (R : ℝ) (hR : 0≤R) (T : ℝ≥0) :
    ∀ᵐ r ∂timeLaw T,∀ᵐ w ∂μ,
      (fieldEmbedding T (realInput T (exitDerivativeInput p R T)) ((r,w.1),w.2):ℂ)+
        Complex.I*(fieldEmbedding T (imagInput T (exitDerivativeInput p R T)) ((r,w.1),w.2):ℂ)=
      {w : Sample | (r.toNNReal:WithTop ℝ≥0)≤exitTime R w}.indicator
        (fun w => p.derivative.eval (value r.toNNReal w)) w := by
  let φ := extension p R false
  let ψ := extension p R true
  have hφ : ∀ z : ℂ,‖z‖≤R → φ z=(p.derivative.eval z).re := extension_agrees p R false
  have hψ : ∀ z : ℂ,‖z‖≤R → ψ z=(p.derivative.eval z).im := extension_agrees p R true
  let τ := clippedClock T (exitTime R)
  have hτ := clippedClock_stopping T (exitTime R) (exitTime_stopping R)
  simp only [exitDerivativeInput,derivativeInput,realInput_combine,imagInput_combine]
  filter_upwards [StochasticCauchyStoppedCoefficients.stoppedInput_physical φ τ hτ T,
    StochasticCauchyStoppedCoefficients.stoppedInput_physical ψ τ hτ T,
    ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr hi hin
  have hrT : r.toNNReal≤T := Real.toNNReal_le_iff_le_coe.mpr hin.2
  filter_upwards [hr,hi,exit_bounded_ae R hR r.toNNReal] with w hr hi hb
  change fieldEmbedding T (W φ τ hτ T) ((r,w.1),w.2)=_ at hr
  change fieldEmbedding T (W ψ τ hτ T) ((r,w.1),w.2)=_ at hi
  have he : r≤(τ w:ℝ) ↔ (r.toNNReal:WithTop ℝ≥0)≤exitTime R w := by
    rw [← Real.toNNReal_le_iff_le_coe]
    change r.toNNReal≤clippedClock T (exitTime R) w ↔ _
    rw [← WithTop.coe_le_coe,clippedClock_coe,le_min_iff]
    simp only [WithTop.coe_le_coe,hrT,and_true]
  have hdisc (hh : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w) : ‖value r.toNNReal w‖≤R := by
    have hc : clippedClock r.toNNReal (exitTime R) w=r.toNNReal := by
      apply WithTop.coe_injective
      rw [clippedClock_coe,min_eq_right hh]
    simpa only [hc] using hb
  change (fieldEmbedding T (W φ τ hτ T) ((r,w.1),w.2):ℂ)+
    Complex.I*(fieldEmbedding T (W ψ τ hτ T) ((r,w.1),w.2):ℂ)=_
  rw [hr,hi]
  by_cases hh : (r.toNNReal:WithTop ℝ≥0)≤exitTime R w
  · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_true]
    rw [hφ _ (hdisc hh),hψ _ (hdisc hh)]
    simpa only [mul_comm] using Complex.re_add_im (p.derivative.eval (value r.toNNReal w))
  · simp only [Set.indicator,Set.mem_Ioc,hin.1,true_and,he,Set.mem_ofPred_eq,hh,ite_false,Complex.ofReal_zero,mul_zero,add_zero]

theorem sampled_polynomial_memLp (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    MemLp (fun w => p.eval (value (clippedClock T (exitTime R) w) w)-p.eval 0) 2 μ :=
  (Lp.memLp (channel T false (((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R T))).ae_eq (exit_polynomial_ito p R T)

/-- SourceL2 class defined by the ACTUAL stopped polynomial difference. -/
def sampledPolynomial (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) : JointComplex :=
  (sampled_polynomial_memLp p R T).toLp _

theorem sampledPolynomial_actual (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    sampledPolynomial p R T =ᵐ[μ] fun w => p.eval (value (clippedClock T (exitTime R) w) w)-p.eval 0 :=
  MemLp.coeFn_toLp _

theorem sampledPolynomial_reconstruction (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R T)=sampledPolynomial p R T :=
  Lp.ext ((exit_polynomial_ito p R T).trans (sampledPolynomial_actual p R T).symm)

/-- Strongest native causal reconstruction here: actual polynomial output,
actual stopped derivative coefficient, canonical channel adjoints and no anti channel. -/
theorem sampledPolynomial_canonical (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    channelAdjoint T false (sampledPolynomial p R T)=((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R T ∧
      channelAdjoint T true (sampledPolynomial p R T)=0 := by
  have h := channel_coefficients_recover T (((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R T) 0
  simpa only [map_zero,add_zero,sampledPolynomial_reconstruction p R T] using h

/-- Native isometry gives the genuine factor2 energy, with actual stopped samples. -/
theorem sampledPolynomial_energy (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    ‖sampledPolynomial p R T‖^2=2*‖exitDerivativeInput p R T‖^2 := by
  rw [← sampledPolynomial_reconstruction,(channel T false).norm_map,norm_smul,mul_pow,
    Complex.norm_real,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

private theorem exit_before (R : ℝ) (T : ℝ≥0) :
    ∀ s w,s<clippedClock T (exitTime R) w → ‖value s w‖≤R := by
  intro s w hs
  have hc : (s:WithTop ℝ≥0)<exitTime R w := (WithTop.coe_lt_coe.mpr hs).trans_le (by
    rw [clippedClock_coe]
    exact min_le_left _ _)
  exact (before_exit R w s hc).le

private theorem exit_grid_actual (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) (n : ℕ) :
    channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid (extension p R false) (extension p R true)
      (clippedClock T (exitTime R)) (clippedClock_stopping T _ (exitTime_stopping R)) T n)
      =ᵐ[μ] derivativeSum (clippedClock T (exitTime R)) T p n :=
  derivativeGrid_actual (extension p R false) (extension p R true) (clippedClock T (exitTime R))
    (clippedClock_stopping T _ (exitTime_stopping R)) T p R
    (extension_agrees p R false) (extension_agrees p R true) (exit_before R T) n

private theorem exit_grid_tendsto (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid (extension p R false) (extension p R true)
      (clippedClock T (exitTime R)) (clippedClock_stopping T _ (exitTime_stopping R)) T n)) atTop
      (𝓝 (sampledPolynomial p R T)) := by
  have hi : Tendsto (fun n => channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid (extension p R false) (extension p R true)
      (clippedClock T (exitTime R)) (clippedClock_stopping T _ (exitTime_stopping R)) T n)) atTop
      (𝓝 (channel T false (((Real.sqrt 2:ℝ):ℂ) • exitDerivativeInput p R T))) :=
    ((channel T false).continuous.tendsto _).comp (tendsto_const_nhds.smul
      (derivativeGrid_tendsto (extension p R false) (extension p R true) (clippedClock T (exitTime R))
        (clippedClock_stopping T _ (exitTime_stopping R)) T))
  rwa [sampledPolynomial_reconstruction] at hi

/-- Actual unclamped derivative chronological sums are genuinely square integrable. -/
theorem exit_derivative_sums_memLp (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) (n : ℕ) :
    MemLp (derivativeSum (clippedClock T (exitTime R)) T p n) 2 μ :=
  (Lp.memLp (channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid (extension p R false) (extension p R true)
    (clippedClock T (exitTime R)) (clippedClock_stopping T _ (exitTime_stopping R)) T n))).ae_eq (exit_grid_actual p R T n)

/-- Physical mean-square convergence to the ACTUAL stopped terminal polynomial,
with the full crossing cell, correct coefficient p-prime and no missing drift. -/
theorem exit_derivative_sums_mean_square (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    Tendsto (fun n => ∫ w,‖derivativeSum (clippedClock T (exitTime R)) T p n w-
      (p.eval (value (clippedClock T (exitTime R) w) w)-p.eval 0)‖^2 ∂μ) atTop (𝓝 0) := by
  let Q : ℕ → JointComplex := fun n => channel T false (((Real.sqrt 2:ℝ):ℂ) • derivativeGrid (extension p R false) (extension p R true)
    (clippedClock T (exitTime R)) (clippedClock_stopping T _ (exitTime_stopping R)) T n)
  have hl : Tendsto Q atTop (𝓝 (sampledPolynomial p R T)) := exit_grid_tendsto p R T
  have hn : Tendsto (fun n => ‖Q n-sampledPolynomial p R T‖^2) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      ((hl.sub_const (sampledPolynomial p R T)).norm.pow 2)
  have he (n : ℕ) : ‖Q n-sampledPolynomial p R T‖^2=
      ∫ w,‖derivativeSum (clippedClock T (exitTime R)) T p n w-
        (p.eval (value (clippedClock T (exitTime R) w) w)-p.eval 0)‖^2 ∂μ := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (Q n) (sampledPolynomial p R T),exit_grid_actual p R T n,
      sampledPolynomial_actual p R T] with w hs hg hp
    change Q n w=_ at hg
    change ‖(Q n-sampledPolynomial p R T) w‖^2=_
    rw [hs]
    simp only [Pi.sub_apply]
    rw [hg,hp]
  simpa only [he] using hn

/-- Actual-source variance equals native derivative energy with its proved factor2. -/
theorem exit_polynomial_variance_energy (p : Polynomial ℂ) (R : ℝ) (T : ℝ≥0) :
    (∫ w,‖p.eval (value (clippedClock T (exitTime R) w) w)-p.eval 0‖^2 ∂μ)=
      2*‖exitDerivativeInput p R T‖^2 := by
  rw [← sampledPolynomial_energy,BochnerL2Dominated.norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [sampledPolynomial_actual p R T] with w hw
  change ‖p.eval (value (clippedClock T (exitTime R) w) w)-p.eval 0‖^2=‖sampledPolynomial p R T w‖^2
  rw [hw]

end OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedPolynomialIto
