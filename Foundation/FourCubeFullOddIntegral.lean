import Foundation.FourCubeFullOddEnvelope

/-! Genuine full32 signed odd-density convergence under an integrable envelope. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullOddIntegral
open QuaternionSU2Representation SU2QuaternionOddWord SU2TraceHessianModel
open OneSidedCapComplex OneSidedBlockRank
open FourCubeFullChartOdd FourCubeFullChartQuadratic FourCubeFullChartDomination
open FourCubeFullHaarCoordinates FourCubeFullHaarCutoff FourCubeFullHaarGaussianLimit
open FourCubeFullOddEnvelope
attribute [local irreducible] OneSidedBlockIncidence.edges OneSidedBlockIncidence.innerFaces OneSidedBlockIncidence.upperFaces

theorem completed_boltzmann_odd_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (-completedRay Y x y z t/t^2)-
      Real.exp (-completedRay Y x y z (-t)/t^2))/(2*t)) (𝓝[≠] 0)
      (𝓝 (-cubicCoefficient Y x y z*Real.exp (-completedQuadratic Y x y z/2))) := by
  let A := fun t : ℝ => completedRay Y x y z t/t^2
  let O := fun t : ℝ => (completedRay Y x y z t-completedRay Y x y z (-t))/(2*t^3)
  let B := fun t : ℝ => A t-2*t*O t
  let D := fun t : ℝ => -2*t*O t
  have ha : Tendsto A (𝓝[≠] 0) (𝓝 (completedQuadratic Y x y z/2)) := completed_quadratic_limit Y x y z
  have ho : Tendsto O (𝓝[≠] 0) (𝓝 (cubicCoefficient Y x y z)) := completed_odd_limit Y x y z
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto D (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (ht.const_mul (-2)).mul ho
  have hb : Tendsto B (𝓝[≠] 0) (𝓝 (completedQuadratic Y x y z/2)) := by
    simpa only [mul_zero,zero_mul,sub_zero] using ha.sub ((ht.const_mul 2).mul ho)
  have hs : Tendsto (fun t => dslope Real.exp 0 (D t)) (𝓝[≠] 0) (𝓝 1) := by
    have hc := (continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt).tendsto.comp hd
    convert! hc using 1 <;> simp [dslope_same,Real.deriv_exp,Function.comp_def]
  have he := Real.continuous_exp.continuousAt.tendsto.comp hb.neg
  have hh := ((he.mul hs).mul ho).neg
  simp only [mul_one] at hh
  have htarget : -(Real.exp (-(completedQuadratic Y x y z/2))*cubicCoefficient Y x y z)=
      -cubicCoefficient Y x y z*Real.exp (-completedQuadratic Y x y z/2) := by rw [neg_div]; ring
  rw [htarget] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t htn
  have htn' : t ≠ 0 := htn
  have hbval : B t=completedRay Y x y z (-t)/t^2 := by
    dsimp [B,A,O]
    field_simp [htn']
    ring
  have hdiff := sub_smul_dslope Real.exp 0 (D t)
  simp only [sub_zero,smul_eq_mul,Real.exp_zero] at hdiff
  have hexp : Real.exp (-A t)=Real.exp (-B t)*Real.exp (D t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [A,B,D]
    ring
  change -(Real.exp (-B t)*dslope Real.exp 0 (D t)*O t)=_
  calc
    _ = Real.exp (-B t)*(D t*dslope Real.exp 0 (D t))/(2*t) := by
      dsimp [D]
      field_simp [htn'] <;> ring
    _ = Real.exp (-B t)*(Real.exp (D t)-1)/(2*t) := by rw [hdiff]
    _ = (Real.exp (-A t)-Real.exp (-B t))/(2*t) := by rw [hexp]; ring
    _ = _ := by rw [hbval]; simp only [A,neg_div]

def oddDensity (t x y z : ℝ) (Y : Coordinates) : ℝ :=
  (thermalDensity x y z t Y-thermalDensity x y z (-t) Y)/(2*t)
def firstDensity (x y z : ℝ) (Y : Coordinates) : ℝ :=
  -cubicCoefficient Y x y z*gaussianDensity x y z Y
def envelope (x y z : ℝ) (Y : Coordinates) : ℝ :=
  (1728*productDensity 0)*((budget Y x y z)^3*Real.exp (-mass Y/4))

theorem productDensity_even (t : ℝ) (Y : Coordinates) :
    productDensity ((-t) • Y)=productDensity (t • Y) := by
  unfold productDensity SU2GaussianConeCoordinates.chartDensity SU2GaussianConeCoordinates.chartRate
  simp [Pi.smul_apply,smul_eq_mul]

theorem oddDensity_formula (t x y z : ℝ) (Y : Coordinates)
    (hY : t • Y∈coordinateCutoff) :
    oddDensity t x y z Y=productDensity (t • Y)*
      ((Real.exp (-completedRay Y x y z t/t^2)-
        Real.exp (-completedRay Y x y z (-t)/t^2))/(2*t)) := by
  have hn := (cutoff_neg t Y).mpr hY
  unfold oddDensity thermalDensity scaledDensity density
  rw [Set.indicator_of_mem hY,Set.indicator_of_mem hn,productDensity_even]
  change (productDensity (t • Y)*Real.exp (-(1/t^2)*completedRay Y x y z t)-
    productDensity (t • Y)*Real.exp (-(1/(-t)^2)*completedRay Y x y z (-t)))/(2*t)=_
  simp only [neg_sq]
  have he (v : ℝ) : -(1/t^2)*v= -v/t^2 := by ring
  simp only [he]
  ring

theorem oddDensity_bound (t x y z : ℝ) (ht : t ≠ 0) (Y : Coordinates) :
    |oddDensity t x y z Y| ≤ envelope x y z Y := by
  classical
  by_cases hY : t • Y∈coordinateCutoff
  · rw [oddDensity_formula t x y z Y hY,abs_mul,
      abs_of_nonneg (productDensity_positive _).le]
    have hb := completed_boltzmann_odd_bound Y x y z t ht hY
    calc
      _ ≤ productDensity 0*((1728*(budget Y x y z)^3)*Real.exp (-mass Y/4)) :=
        mul_le_mul (productDensity_le_zero _) hb (abs_nonneg _) (productDensity_positive _).le
      _ = _ := by unfold envelope; ring
  · have hn := mt (cutoff_neg t Y).mp hY
    simp only [oddDensity,thermalDensity,scaledDensity,density,
      Set.indicator_of_notMem hY,Set.indicator_of_notMem hn,sub_self,zero_div,abs_zero]
    unfold envelope
    have hp := (budget_positive Y x y z).le
    have hd := (productDensity_positive (0 : Coordinates)).le
    positivity

theorem envelope_integrable (x y z : ℝ) : Integrable (envelope x y z) :=
  (cubic_weight_integrable x y z).const_mul _

theorem oddDensity_tendsto (x y z : ℝ) (Y : Coordinates) :
    Tendsto (fun t : ℝ => oddDensity t x y z Y) (𝓝[≠] 0) (𝓝 (firstDensity x y z Y)) := by
  have hp := (productDensity_scaled_tendsto Y).mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)
  rw [← productDensity_zero] at hp
  have hh := hp.mul (completed_boltzmann_odd_limit Y x y z)
  have he : productDensity 0*(-cubicCoefficient Y x y z*
      Real.exp (-completedQuadratic Y x y z/2))=firstDensity x y z Y := by
    unfold firstDensity gaussianDensity
    ring
  rw [he] at hh
  apply hh.congr'
  filter_upwards [(eventually_cutoff Y).filter_mono nhdsWithin_le_nhds] with t ht
  exact (oddDensity_formula t x y z Y ht).symm

theorem cubicCoefficient_measurable (x y z : ℝ) :
    Measurable (fun Y : Coordinates => cubicCoefficient Y x y z) := by
  have hr (e : FullEdge) :
      Measurable (fun Y : Coordinates => rawVelocity Y x y z e) := by
    cases e with
    | inl e => exact measurable_pi_apply e
    | inr c => exact measurable_const
  have hv (p : FullFace) : Measurable (fun Y : Coordinates => vectors Y x y z p) := by
    apply measurable_pi_iff.mpr
    intro i
    fin_cases i <;> simp only [vectors,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk] <;> first | exact hr _ | exact (hr _).neg
  unfold cubicCoefficient
  apply Finset.measurable_sum
  intro p _
  exact weightedCubic_continuous.measurable.comp
    ((measurable_const : Measurable (fun _ : Coordinates => (fun _ : Fin 4 => (1 : ℝ)))).prodMk (hv p))

theorem firstDensity_measurable (x y z : ℝ) : Measurable (firstDensity x y z) :=
  (cubicCoefficient_measurable x y z).neg.mul (gaussianDensity_continuous x y z).measurable

theorem firstDensity_bound (x y z : ℝ) (Y : Coordinates) :
    |firstDensity x y z Y| ≤ envelope x y z Y := by
  apply le_of_tendsto (oddDensity_tendsto x y z Y).abs
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact oddDensity_bound t x y z ht Y

theorem firstDensity_integrable (x y z : ℝ) : Integrable (firstDensity x y z) := by
  apply (envelope_integrable x y z).mono' (firstDensity_measurable x y z).aestronglyMeasurable
  exact ae_of_all _ (fun Y => by rw [Real.norm_eq_abs]; exact firstDensity_bound x y z Y)

theorem oddDensity_integrable (t x y z : ℝ) (ht : t ≠ 0) : Integrable (oddDensity t x y z) :=
  ((scaledDensity_integrable _ _ t ht).sub
    (scaledDensity_integrable _ _ (-t) (neg_ne_zero.mpr ht))).div_const _

theorem oddDensity_integral_tendsto (x y z : ℝ) :
    Tendsto (fun t : ℝ => ∫ Y : Coordinates,oddDensity t x y z Y) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,firstDensity x y z Y)) := by
  apply tendsto_integral_filter_of_dominated_convergence (envelope x y z)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact (oddDensity_integrable t x y z ht).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ae_of_all _ (fun Y => by rw [Real.norm_eq_abs]; exact oddDensity_bound t x y z ht Y)
  · exact envelope_integrable x y z
  · exact ae_of_all _ (oddDensity_tendsto x y z)

theorem scaled_density_integral_odd_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => ((∫ Y : Coordinates,thermalDensity x y z t Y)-
      (∫ Y : Coordinates,thermalDensity x y z (-t) Y))/(2*t)) (𝓝[≠] 0)
      (𝓝 (∫ Y : Coordinates,firstDensity x y z Y)) := by
  apply (oddDensity_integral_tendsto x y z).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [oddDensity,integral_div]
  unfold thermalDensity
  rw [integral_sub (scaledDensity_integrable _ _ t ht)
    (scaledDensity_integrable _ _ (-t) (neg_ne_zero.mpr ht))]

open FourCubeFullColorSymmetry

theorem firstDensity_sign_sum (x y z : ℝ) (Y : Coordinates) :
    (∑ s : FourCubeColorReflection.Signs,
      firstDensity x y z (affine s (FourCubeFullQuadraticCenter.center x y z) Y))=
      (-8*cubicCoefficient (FourCubeFullQuadraticCenter.center x y z) x y z)*
        gaussianDensity x y z Y := by
  simp only [firstDensity,neg_mul]
  rw [Finset.sum_neg_distrib,weighted_cubic_sign_sum]

theorem firstDensity_integral_value (x y z : ℝ) :
    (∫ Y : Coordinates,firstDensity x y z Y)=
      -(((1784975 : ℝ)/2750517)*x*y*z)*(∫ Y : Coordinates,gaussianDensity x y z Y) := by
  have hi (s : FourCubeColorReflection.Signs) :
      Integrable (fun Y : Coordinates => firstDensity x y z
        (affine s (FourCubeFullQuadraticCenter.center x y z) Y)) :=
    (affine_preserving s _).integrable_comp_of_integrable (firstDensity_integrable x y z)
  have hh : 8*(∫ Y : Coordinates,firstDensity x y z Y)=
      (-8*cubicCoefficient (FourCubeFullQuadraticCenter.center x y z) x y z)*
        (∫ Y : Coordinates,gaussianDensity x y z Y) := calc
    _ = ∑ s : FourCubeColorReflection.Signs,∫ Y : Coordinates,firstDensity x y z
        (affine s (FourCubeFullQuadraticCenter.center x y z) Y) := by
      simp only [integral_affine,Finset.sum_const,Finset.card_univ,
        Fintype.card_prod,Fintype.card_bool,nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
      ring
    _ = ∫ Y : Coordinates,∑ s : FourCubeColorReflection.Signs,firstDensity x y z
        (affine s (FourCubeFullQuadraticCenter.center x y z) Y) :=
      (integral_finsetSum Finset.univ (fun s _ => hi s)).symm
    _ = _ := by simp_rw [firstDensity_sign_sum]; rw [integral_const_mul]
  rw [center_cubic_amplitudes] at hh
  linarith

theorem scaled_density_integral_odd_value (x y z : ℝ) :
    Tendsto (fun t : ℝ => ((∫ Y : Coordinates,thermalDensity x y z t Y)-
      (∫ Y : Coordinates,thermalDensity x y z (-t) Y))/(2*t)) (𝓝[≠] 0)
      (𝓝 (-(((1784975 : ℝ)/2750517)*x*y*z)*
        (∫ Y : Coordinates,gaussianDensity x y z Y))) := by
  rw [← firstDensity_integral_value]
  exact scaled_density_integral_odd_limit x y z

theorem actual_cutoff_partition_odd_value (x y z : ℝ) :
    Tendsto (fun t : ℝ => (localPartition (parameters x y z t) (1/t^2)-
      localPartition (parameters x y z (-t)) (1/t^2))/(2*t*|t|^96)) (𝓝[≠] 0)
      (𝓝 (-(((1784975 : ℝ)/2750517)*x*y*z)*
        (∫ Y : Coordinates,gaussianDensity x y z Y))) := by
  apply (scaled_density_integral_odd_value x y z).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [localPartition_rescale _ _ t ht,
    localPartition_rescale _ _ (-t) (neg_ne_zero.mpr ht),abs_neg]
  unfold thermalDensity
  simp only [neg_sq]
  field_simp [ht,abs_ne_zero.mpr ht] <;> ring

theorem normalized_firstDensity_integral (x y z : ℝ) :
    (∫ Y : Coordinates,firstDensity x y z Y)/(∫ Y : Coordinates,gaussianDensity x y z Y)=
      -(((1784975 : ℝ)/2750517)*x*y*z) := by
  rw [firstDensity_integral_value,
    mul_div_cancel_right₀ _ (gaussian_integral_positive x y z).ne']

end OperatorDerivativeRewrite.Foundation.FourCubeFullOddIntegral
