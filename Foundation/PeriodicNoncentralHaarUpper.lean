import Foundation.SU2TransverseHaar
/-! Actual full64-variable Haar191-power upper control at a specified
noncentral winding. A quarter-coupling split combines the verified relative
Gaussian envelope with actual transverse-root Haar integration. Constants
are explicit, coarse and degenerate at central winding. No matching lower
bound, exact coefficient, stationary normalization or physical gap is claimed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicNoncentralHaarUpper
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereJets
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicGaugeSaturatedGround
open PeriodicFlatBackgroundHessian PeriodicTransportedRoot PeriodicRootHaarControl
open PeriodicRootedHaarControl (chartState budget)

private def halfVelocity (X : Velocity) : Velocity := (1/2 : ℝ) • X

private theorem chart_half (H : State) (X : Velocity) (t : ℝ) :
    chartState H (halfVelocity X) (2*t)=chartState H X t := by
  funext e
  unfold chartState halfVelocity
  simp only [Pi.smul_apply,smul_smul]
  rw [show (2*t)*(1/2 : ℝ)=t by ring]

private theorem exponential_split (A B R : ℝ)
    (h : Real.exp (-A)≤Real.exp B*Real.exp (-R)) :
    Real.exp (-A)≤Real.exp (3*B/4)*Real.exp (-3*R/4)*Real.exp (-A/4) := by
  rw [← Real.exp_add] at h
  have hh := Real.exp_le_exp.mp h
  rw [← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

private def scaledAction (H : State) (X Y : Velocity) (t : ℝ) (p : SU2 × RelField) : ℝ :=
  halfAction (chartState H X t) (chartState H Y t) (fromCoordinates H p)/t^2

private theorem integrand_exp (H : State) (X Y : Velocity) (t : ℝ) (p : SU2 × RelField) :
    integrand H X Y t p=Real.exp (-scaledAction H X Y t p) := by
  unfold integrand PeriodicWilsonSlab.weight scaledAction
  congr 1
  ring

private theorem integrand_quarter (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (p : SU2 × RelField) :
    integrand H (halfVelocity X) (halfVelocity Y) (2*t) p=Real.exp (-scaledAction H X Y t p/4) := by
  unfold integrand
  rw [chart_half,chart_half]
  unfold PeriodicWilsonSlab.weight scaledAction
  congr 1
  field_simp
  ring

private theorem mismatch_axis (H : State) (i : Fin 3) (θ : ℝ)
    (hw : PeriodicSpatialHolonomy.winding H root i=SU2JointPlaquetteCubic.axis 0 θ) (c : SU2) :
    mismatchRate H i c=Real.sin θ^2*SU2TransverseHaar.transverse c/24 := by
  have he : mismatchRate H i c=SU2TwoAxisStabilizerHaar.turn 0 θ c^2/96 := by
    unfold mismatchRate SU2TwoAxisStabilizerHaar.turn
    rw [hw]
    unfold PeriodicLoopVariation.distance
    rw [norm_sub_rev]
  rw [he,SU2TwoAxisStabilizerHaar.turn_zero_square]
  unfold SU2TransverseHaar.transverse
  ring

private theorem integrand_split (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0)
    (i : Fin 3) (θ : ℝ) (hw : PeriodicSpatialHolonomy.winding H root i=SU2JointPlaquetteCubic.axis 0 θ)
    (c : SU2) (r : RelField) :
    integrand H X Y t (c,r)≤Real.exp (3*budget X Y/4)*
      SU2TransverseHaar.gaussian (Real.sin θ^2/(32*t^2)) c*
        integrand H (halfVelocity X) (halfVelocity Y) (2*t) (c,r) := by
  have hh := mismatch_weight_bound H X Y t ht i c r
  rw [integrand_exp] at hh
  have he := exponential_split (scaledAction H X Y t (c,r)) (budget X Y) (mismatchRate H i c/t^2)
    (by simpa only [neg_div] using hh)
  have hm : Real.exp (-3*(mismatchRate H i c/t^2)/4)=
      SU2TransverseHaar.gaussian (Real.sin θ^2/(32*t^2)) c := by
    rw [mismatch_axis H i θ hw]
    unfold SU2TransverseHaar.gaussian
    congr 1
    field_simp
    ring
  rw [hm,← integrand_exp,← integrand_quarter H X Y t ht (c,r)] at he
  exact he

def relativeFactor (X Y : Velocity) (t : ℝ) : ℝ :=
  gaussianBound (halfVelocity X) (halfVelocity Y)+tailBound (halfVelocity X) (halfVelocity Y) (2*t)

private theorem gaussianBound_nonneg (X Y : Velocity) : 0≤gaussianBound X Y := by
  unfold gaussianBound
  apply integral_nonneg
  intro Z
  unfold PeriodicAnchoredHaarLimit.majorant
  exact mul_nonneg (PeriodicFullHaarGaussianLimit.density_nonneg _) (by positivity)

private theorem relativeFactor_nonneg (X Y : Velocity) (t : ℝ) : 0≤relativeFactor X Y t := by
  unfold relativeFactor
  apply add_nonneg (gaussianBound_nonneg _ _)
  unfold tailBound
  positivity

private theorem quarter_block_bound (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (c : SU2) :
    rootBlock H (halfVelocity X) (halfVelocity Y) (2*t) c≤|2*t|^189*relativeFactor X Y t := by
  have hh := rootBlock_scaled_bound H (halfVelocity X) (halfVelocity Y) (2*t)
    (mul_ne_zero (by norm_num) ht) c
  have hp : 0 < |2*t|^189 := pow_pos (abs_pos.mpr (mul_ne_zero (by norm_num) ht)) _
  have he := (div_le_iff₀ hp).mp hh
  unfold relativeFactor
  nlinarith

private theorem rootBlock_split (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0)
    (i : Fin 3) (θ : ℝ) (hw : PeriodicSpatialHolonomy.winding H root i=SU2JointPlaquetteCubic.axis 0 θ)
    (c : SU2) :
    rootBlock H X Y t c≤(Real.exp (3*budget X Y/4)*|2*t|^189*relativeFactor X Y t)*
      SU2TransverseHaar.gaussian (Real.sin θ^2/(32*t^2)) c := by
  have hh := integral_mono (section_integrable H X Y t c)
    ((section_integrable H (halfVelocity X) (halfVelocity Y) (2*t) c).const_mul
      (Real.exp (3*budget X Y/4)*SU2TransverseHaar.gaussian (Real.sin θ^2/(32*t^2)) c))
    (integrand_split H X Y t ht i θ hw c)
  rw [integral_const_mul] at hh
  have he := mul_le_mul_of_nonneg_left (quarter_block_bound H X Y t ht c)
    (by unfold SU2TransverseHaar.gaussian; positivity : 0≤Real.exp (3*budget X Y/4)*
      SU2TransverseHaar.gaussian (Real.sin θ^2/(32*t^2)) c)
  change rootBlock H X Y t c≤_ at hh
  convert hh.trans he using 1 <;> ring

theorem kernel_upper (H : State) (X Y : Velocity) (t : ℝ) (ht : t≠0) (i : Fin 3) (θ : ℝ)
    (hw : PeriodicSpatialHolonomy.winding H root i=SU2JointPlaquetteCubic.axis 0 θ)
    (hθ : Real.sin θ≠0) :
    kernel (1/t^2) (chartState H X t) (chartState H Y t)≤
      (Real.exp (3*budget X Y/4)*|2*t|^189*relativeFactor X Y t)*
        (1024*t^2/(Real.pi*Real.sin θ^2)+Real.exp (-Real.sin θ^2/(64*t^2))) := by
  let s := Real.sin θ^2/(32*t^2)
  have hs : 0<s := div_pos (sq_pos_of_ne_zero hθ) (mul_pos (by norm_num) (sq_pos_of_ne_zero ht))
  let C := Real.exp (3*budget X Y/4)*|2*t|^189*relativeFactor X Y t
  have hC : 0≤C := mul_nonneg (by positivity) (relativeFactor_nonneg X Y t)
  have hh := integral_mono (rootBlock_integrable H X Y t)
    ((SU2TransverseHaar.gaussian_integrable s hs.le).const_mul C)
    (rootBlock_split H X Y t ht i θ hw)
  rw [integral_const_mul] at hh
  change (∫ c,rootBlock H X Y t c ∂law)≤C*SU2TransverseHaar.mass s at hh
  rw [← kernel_root_integral] at hh
  have he := mul_le_mul_of_nonneg_left (SU2TransverseHaar.mass_upper s hs) hC
  have h0 : 32/(Real.pi*s)=1024*t^2/(Real.pi*Real.sin θ^2) := by
    unfold s
    field_simp
    ring
  have h1 : -s/2= -Real.sin θ^2/(64*t^2) := by unfold s; ring
  rw [h0,h1] at he
  exact hh.trans he


private theorem double_scale_tendsto : Tendsto (fun t : ℝ => 2*t) (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => 2*t) := continuous_const.mul continuous_id
    simpa only [mul_zero] using hc.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ)≤𝓝 0)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_ne_zero (by norm_num) ht

private theorem exponential_over_square_limit (a : ℝ) (ha : 0<a) :
    Tendsto (fun t : ℝ => Real.exp (-a/t^2)/t^2) (𝓝[≠] 0) (𝓝 0) := by
  have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a ha).comp
    FourCubeHaarPartitionAsymptotic.inverse_square_tendsto
  simp only [Real.rpow_one,Function.comp_def] at hh
  apply hh.congr'
  filter_upwards [] with t
  rw [show -a*(1/t^2)= -a/t^2 by ring]
  ring

def upperConstant (X Y : Velocity) (θ : ℝ) : ℝ :=
  (2 : ℝ)^189*Real.exp (3*budget X Y/4)*(gaussianBound (halfVelocity X) (halfVelocity Y)+1)*
    (1024/(Real.pi*Real.sin θ^2)+1)

theorem upperConstant_pos (X Y : Velocity) (θ : ℝ) : 0<upperConstant X Y θ := by
  have h := gaussianBound_nonneg (halfVelocity X) (halfVelocity Y)
  unfold upperConstant
  positivity

/-- A genuine full64-variable Haar191-power UPPER bound, not a matching
lower bound, exact prefactor, stationary normalization or physical gap. -/
theorem kernel_eventual_power_bound (H : State) (X Y : Velocity) (i : Fin 3) (θ : ℝ)
    (hw : PeriodicSpatialHolonomy.winding H root i=SU2JointPlaquetteCubic.axis 0 θ)
    (hθ : Real.sin θ≠0) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,kernel (1/t^2) (chartState H X t) (chartState H Y t)≤upperConstant X Y θ*|t|^191 := by
  have htail := (tailBound_limit (halfVelocity X) (halfVelocity Y)).comp double_scale_tendsto
  have hexp : Tendsto (fun t : ℝ => Real.exp (-Real.sin θ^2/(64*t^2))/t^2) (𝓝[≠] 0) (𝓝 0) := by
    have hh := exponential_over_square_limit (Real.sin θ^2/64) (by positivity)
    convert hh using 1
    funext t
    congr 2
    ring
  filter_upwards [self_mem_nhdsWithin,htail.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hexp.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))] with t ht ht' he'
  have hpoly : Real.exp (-Real.sin θ^2/(64*t^2))≤t^2 :=
    by simpa only [one_mul] using (div_le_iff₀ (sq_pos_of_ne_zero ht)).mp he'.le
  change tailBound (halfVelocity X) (halfVelocity Y) (2*t)<1 at ht'
  have hrel : relativeFactor X Y t≤gaussianBound (halfVelocity X) (halfVelocity Y)+1 := by
    unfold relativeFactor
    linarith
  have hg := gaussianBound_nonneg (halfVelocity X) (halfVelocity Y)
  have h1 := mul_le_mul_of_nonneg_left hrel
    (by positivity : 0≤Real.exp (3*budget X Y/4)*|2*t|^189)
  have h2 : 1024*t^2/(Real.pi*Real.sin θ^2)+Real.exp (-Real.sin θ^2/(64*t^2))≤
      1024*t^2/(Real.pi*Real.sin θ^2)+t^2 := by linarith
  have hb := mul_le_mul h1 h2 (by positivity) (by positivity)
  calc
    _ ≤ (Real.exp (3*budget X Y/4)*|2*t|^189*relativeFactor X Y t)*
        (1024*t^2/(Real.pi*Real.sin θ^2)+Real.exp (-Real.sin θ^2/(64*t^2))) :=
      kernel_upper H X Y t ht i θ hw hθ
    _ ≤ _ := hb
    _ = upperConstant X Y θ*|t|^191 := by
      unfold upperConstant
      rw [abs_mul,show |(2 : ℝ)|=2 by norm_num,mul_pow,
        show (191 : ℕ)=189+2 by decide,pow_add,sq_abs]
      ring

theorem commonAxis_eventual_power_bound (α : Fin 3 → ℝ) (X Y : Velocity) (i : Fin 3)
    (hi : Real.sin (4*α i)≠0) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,kernel (1/t^2)
      (chartState (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) X t)
      (chartState (PeriodicAnchoredHaarLimit.base (PeriodicChargedFourier.background α)) Y t)≤
        upperConstant X Y (4*α i)*|t|^191 :=
  kernel_eventual_power_bound _ X Y i (4*α i) (commonAxis_winding α i) hi

end OperatorDerivativeRewrite.Foundation.PeriodicNoncentralHaarUpper
