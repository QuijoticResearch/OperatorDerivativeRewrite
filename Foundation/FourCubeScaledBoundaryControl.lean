import Foundation.FourCubeBoundaryCoercivity

/-! Uniform actual fixed-cell bounds for boundary angles of order beta^(-1/2). -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeScaledBoundaryControl
open QuaternionSU2Representation OneSidedCapComplex FourCubeIntegratedCubic FourCubePinnedHaar
open FourCubePinnedCoercivity FourCubePinnedConcentration FourCubeBoundaryCoercivity
open FourCubeHemisphereCoercivity FourCubeHaarLaplaceDensity FourCubeHaarProductCoordinates
open FourCubePhysicalEnergy

def movingBoundary (t x y z : ℝ) := boundaryData (t*x) (t*y) (t*z)

theorem scaled_boundaryCost (β t : ℝ) (hβ : 0 ≤ β) (ht : β * t^2=1) (x y z : ℝ) :
    β*boundaryCost (movingBoundary t x y z) ≤ 216*(x^2+y^2+z^2) := by
  have hh := mul_le_mul_of_nonneg_left (boundaryCost_upper (t*x) (t*y) (t*z)) hβ
  change β*boundaryCost (movingBoundary t x y z) ≤ _ at hh
  have he : β*(216*((t*x)^2+(t*y)^2+(t*z)^2))=216*(x^2+y^2+z^2) := by
    calc
      _ = (β*t^2)*(216*(x^2+y^2+z^2)) := by ring
      _ = _ := by rw [ht,one_mul]
  rwa [he] at hh

theorem scaled_action_lower (β t : ℝ) (hβ : 0 ≤ β) (ht : β * t^2=1)
    (b : Boundary → SU2) (B : ℝ) (hb : β * boundaryCost b ≤ B)
    (Y : Field) (hY : ∀ e, SU2GaussianConeCoordinates.chartRate (t • Y e) ≤ 2) :
    quadraticMass Y/1116-B ≤ β*perturbedAction b (chartField (t • Y)) := by
  have hv := FourCubeHemisphereCoercivity.scaled_action_lower β t hβ ht Y hY
  have hh := mul_le_mul_of_nonneg_left (perturbedAction_lower b (chartField (t • Y))) hβ
  nlinarith

theorem scaled_boltzmann_bound (β t : ℝ) (hβ : 0 ≤ β) (ht : β * t^2=1)
    (b : Boundary → SU2) (B : ℝ) (hb : β * boundaryCost b ≤ B)
    (Y : Field) (hY : ∀ e, SU2GaussianConeCoordinates.chartRate (t • Y e) ≤ 2) :
    Real.exp (-β*perturbedAction b (chartField (t • Y))) ≤
      Real.exp B*Real.exp (-quadraticMass Y/1116) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith [scaled_action_lower β t hβ ht b B hb Y hY]

theorem moving_boltzmann_bound (β t x y z : ℝ) (hβ : 0 ≤ β) (ht : β * t^2=1)
    (Y : Field) (hY : ∀ e, SU2GaussianConeCoordinates.chartRate (t • Y e) ≤ 2) :
    Real.exp (-β*perturbedAction (movingBoundary t x y z) (chartField (t • Y))) ≤
      Real.exp (216*(x^2+y^2+z^2))*Real.exp (-quadraticMass Y/1116) :=
  scaled_boltzmann_bound β t hβ ht _ _ (scaled_boundaryCost β t hβ ht x y z) Y hY

theorem broadened_gaussian_integrable :
    Integrable (fun Y : Field => Real.exp (-quadraticMass Y/1116)) := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  have hh := gaussian_envelope_integrable.comp_smul (inv_ne_zero hs)
  convert! hh using 1
  funext Y
  rw [quadraticMass_smul]
  congr 1
  rw [inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  ring

def normalizedPartition (β : ℝ) (b : Boundary → SU2) := pinnedPartition β b/normalizer β

theorem normalizedPartition_bounds (β : ℝ) (hβ : 0 ≤ β) (b : Boundary → SU2)
    (B : ℝ) (hb : β * boundaryCost b ≤ B) :
    Real.exp (-3*B)*(normalizer (3*β)/normalizer β) ≤ normalizedPartition β b ∧
      normalizedPartition β b ≤ Real.exp B*(normalizer (β/3)/normalizer β) := by
  have hz := (normalizer_positive β).le
  constructor
  · calc
      _ ≤ Real.exp (-3*β*boundaryCost b)*(normalizer (3*β)/normalizer β) := by
        apply mul_le_mul_of_nonneg_right
        · apply Real.exp_le_exp.mpr
          nlinarith
        · exact div_nonneg (normalizer_positive _).le hz
      _ = (Real.exp (-3*β*boundaryCost b)*normalizer (3*β))/normalizer β := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (pinnedPartition_lower β hβ b) hz
  · calc
      _ ≤ (Real.exp (β*boundaryCost b)*normalizer (β/3))/normalizer β :=
        div_le_div_of_nonneg_right (pinnedPartition_upper β hβ b) hz
      _ = Real.exp (β*boundaryCost b)*(normalizer (β/3)/normalizer β) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hb)
        (div_nonneg (normalizer_positive _).le hz)

theorem moving_partition_bounds (t : ℝ) (ht : t ≠ 0) (x y z R : ℝ)
    (hR : x ^ 2 + y^2+z^2 ≤ R) :
    Real.exp (-648*R)*(normalizer (3/t^2)/normalizer (1/t^2)) ≤
        normalizedPartition (1/t^2) (movingBoundary t x y z) ∧
      normalizedPartition (1/t^2) (movingBoundary t x y z) ≤
        Real.exp (216*R)*(normalizer ((1/3)/t^2)/normalizer (1/t^2)) := by
  have hβ : 0 ≤ 1/t^2 := by positivity
  have hclock : (1/t^2)*t^2=1 := by field_simp
  have hb : (1/t^2)*boundaryCost (movingBoundary t x y z) ≤ 216*R :=
    (scaled_boundaryCost (1/t^2) t hβ hclock x y z).trans (by nlinarith)
  have hh := normalizedPartition_bounds (1/t^2) hβ (movingBoundary t x y z) (216*R) hb
  have h1 : 3*(1/t^2)=3/t^2 := by ring
  have h2 : (1/t^2)/3=(1/3)/t^2 := by ring
  have h3 : -3*(216*R)=-648*R := by ring
  simpa only [h1,h2,h3] using hh

/-- One punctured neighborhood works simultaneously for all amplitudes in the displayed ball. -/
theorem uniform_moving_partition_bounds (R : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x y z : ℝ,x^2+y^2+z^2 ≤ R →
      Real.exp (-648*R)*((Real.sqrt 3)⁻¹^93/2) ≤
          normalizedPartition (1/t^2) (movingBoundary t x y z) ∧
        normalizedPartition (1/t^2) (movingBoundary t x y z) ≤
          Real.exp (216*R)*((Real.sqrt (1/3))⁻¹^93+1) := by
  have hpos : 0 < (Real.sqrt (3 : ℝ))⁻¹^93 := by positivity
  have hl := (partition_ratio_tendsto 3 (by norm_num)).eventually
    (eventually_gt_nhds (show (Real.sqrt (3 : ℝ))⁻¹^93/2 < (Real.sqrt 3)⁻¹^93 by linarith))
  have hu := (partition_ratio_tendsto (1/3) (by norm_num)).eventually
    (eventually_lt_nhds (show (Real.sqrt (1/3 : ℝ))⁻¹^93 < (Real.sqrt (1/3))⁻¹^93+1 by linarith))
  filter_upwards [self_mem_nhdsWithin,hl,hu] with t ht hl hu x y z hR
  have hh := moving_partition_bounds t ht x y z R hR
  exact ⟨(mul_le_mul_of_nonneg_left hl.le (Real.exp_pos _).le).trans hh.1,
    hh.2.trans (mul_le_mul_of_nonneg_left hu.le (Real.exp_pos _).le)⟩

def boundaryScaledDensity (t x y z : ℝ) : Field → ℝ := by
  classical
  exact (scaledCutoff t).indicator (fun Y => productDensity (t • Y)*
    Real.exp (-perturbedAction (movingBoundary t x y z) (chartField (t • Y))/t^2))

theorem boundaryScaledDensity_measurable (t x y z : ℝ) :
    Measurable (boundaryScaledDensity t x y z) := by
  have hm : Measurable (fun Y : Field => t • Y) :=
    (continuous_const_smul t : Continuous (fun Y : Field => t • Y)).measurable
  have hp := (perturbedAction_measurable (movingBoundary t x y z)).comp
    (chartField_measurable.comp hm)
  exact ((productDensity_measurable.comp hm).mul ((hp.neg.div_const _).exp)).indicator
    (scaledCutoff_measurable t)

theorem boundaryScaledDensity_nonneg (t x y z : ℝ) (Y : Field) :
    0 ≤ boundaryScaledDensity t x y z Y := by
  classical
  unfold boundaryScaledDensity
  by_cases h : Y∈scaledCutoff t
  · rw [Set.indicator_of_mem h]
    exact mul_nonneg (productDensity_nonneg _) (Real.exp_pos _).le
  · rw [Set.indicator_of_notMem h]

theorem boundaryScaledDensity_bound (t : ℝ) (ht : t ≠ 0) (x y z R : ℝ)
    (hR : x ^ 2 + y^2+z^2 ≤ R) (Y : Field) :
    boundaryScaledDensity t x y z Y ≤
      (productDensity 0*Real.exp (216*R))*Real.exp (-quadraticMass Y/1116) := by
  classical
  unfold boundaryScaledDensity
  by_cases h : Y∈scaledCutoff t
  · rw [Set.indicator_of_mem h]
    have hβ : 0 ≤ 1/t^2 := by positivity
    have hclock : (1/t^2)*t^2=1 := by field_simp
    have hb : (1/t^2)*boundaryCost (movingBoundary t x y z) ≤ 216*R :=
      (scaled_boundaryCost (1/t^2) t hβ hclock x y z).trans (by nlinarith)
    have he := scaled_boltzmann_bound (1/t^2) t hβ hclock _ (216*R) hb Y h
    have he' : Real.exp (-perturbedAction (movingBoundary t x y z) (chartField (t • Y))/t^2) ≤
        Real.exp (216*R)*Real.exp (-quadraticMass Y/1116) := by
      convert! he using 1
      congr 1
      ring
    calc
      _ ≤ productDensity 0*(Real.exp (216*R)*Real.exp (-quadraticMass Y/1116)) :=
        mul_le_mul (productDensity_le_zero _) he' (Real.exp_pos _).le (productDensity_nonneg _)
      _ = _ := by ring
  · rw [Set.indicator_of_notMem h]
    exact mul_nonneg (mul_nonneg (productDensity_nonneg 0) (Real.exp_pos _).le)
      (Real.exp_pos _).le

theorem boundaryScaledDensity_integrable (t : ℝ) (ht : t ≠ 0) (x y z : ℝ) :
    Integrable (boundaryScaledDensity t x y z) := by
  apply (broadened_gaussian_integrable.const_mul
    (productDensity 0*Real.exp (216*(x^2+y^2+z^2)))).mono'
      (boundaryScaledDensity_measurable t x y z).aestronglyMeasurable
  filter_upwards with Y
  rw [Real.norm_eq_abs,abs_of_nonneg (boundaryScaledDensity_nonneg t x y z Y)]
  exact boundaryScaledDensity_bound t ht x y z _ le_rfl Y

def movingLocalPartition (t x y z : ℝ) : ℝ :=
  ∫ U in localStateDomain,Real.exp (-perturbedAction (movingBoundary t x y z) U/t^2) ∂pinnedHaar

/-- Exact transport of the actual restricted Haar integral, including its93-dimensional Jacobian. -/
theorem movingLocalPartition_rescale (t : ℝ) (ht : t ≠ 0) (x y z : ℝ) :
    movingLocalPartition t x y z=|t|^93*(∫ Y : Field,boundaryScaledDensity t x y z Y) := by
  classical
  have hm : Measurable (fun U : PinnedState =>
      Real.exp (-perturbedAction (movingBoundary t x y z) U/t^2)) :=
    ((perturbedAction_measurable _).neg.div_const (t^2)).exp
  rw [movingLocalPartition,FourCubeHaarPartitionAsymptotic.integral_actual_cutoff _ hm,
    ← integral_indicator coordinateCutoff_measurable]
  let F : Field → ℝ := coordinateCutoff.indicator (fun Z => productDensity Z*
    Real.exp (-perturbedAction (movingBoundary t x y z) (chartField Z)/t^2))
  change (∫ Y : Field,F Y)=_
  rw [integral_rescale F t ht]
  congr 1

end OperatorDerivativeRewrite.Foundation.FourCubeScaledBoundaryControl
