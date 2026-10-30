import Foundation.CubeChordOperator
import Foundation.CubeBoundaryHaarL2

/-! Quantitative off-chart error for the actual full boundary-Haar kernel at t^36 scale. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeBoundaryExterior
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeTemporalSlab CubeWilsonSlab CubeAxialSlice CubeAxialGauge CubeReducedHaar
open FourCubePinnedCoercivity FourCubeHemisphereCoercivity CubeChartAction
attribute [local irreducible] CubeWilsonSlab.kernel defect boundaryHaar

def chordRegion : Set Chords := {q | ∀ i, q i ∈ hemisphere ∧ chartRate (coordinates (q i)) ≤ 2}
def region : Set State := reduced ⁻¹' chordRegion
def discardedKernel (t : ℝ) (p : State × State) : ℝ :=
  (region ×ˢ region)ᶜ.indicator (fun p => kernel (1/t^2) p.1 p.2/t^36) p
def errorConstant : ℝ := CubeMatchedGround.temporalConstant^7*(40320*32^8)

theorem chordRegion_measurable : MeasurableSet chordRegion := by
  have hR : Measurable chartRate := by unfold chartRate; fun_prop
  have hh : MeasurableSet hemisphere := measurableSet_lt measurable_const halfTrace_measurable
  convert MeasurableSet.iInter
    (fun i : Fin 5 => (hh.preimage (measurable_pi_apply i)).inter
      (measurableSet_le (hR.comp (coordinates_measurable.comp (measurable_pi_apply i)))
        (measurable_const : Measurable (fun _ : Chords => (2 : ℝ))))) using 1
  ext q
  simp [chordRegion]

theorem region_measurable : MeasurableSet region := chordRegion_measurable.preimage reduced_measurable

theorem ray_region_iff (X : Boundary) (t : ℝ) :
    boundaryRay X t ∈ region ↔ X ∈ CubeBoundaryKernelL2.cutoff t := by
  simp only [region,Set.mem_preimage,boundaryRay,reduced_axial,chordRegion,Set.mem_setOf_eq,
    chords,chart_mem_hemisphere,coordinates_chart,true_and,CubeBoundaryKernelL2.cutoff]

theorem outside_energy (U : State) (hU : U ∉ region) : 1/16 ≤ spatialAction U := by
  have he : 1/4 ≤ chordEnergy (reduced U) := by
    by_contra h
    have hs : chordEnergy (reduced U) < 1/4 := lt_of_not_ge h
    apply hU
    change ∀ i, reduced U i ∈ hemisphere ∧ chartRate (coordinates (reduced U i)) ≤ 2
    intro i
    have hi : defect (reduced U i) ≤ chordEnergy (reduced U) :=
      Finset.single_le_sum (fun j _ => defect_nonneg (reduced U j)) (Finset.mem_univ i)
    have hl : defect (reduced U i) < 1/4 := hi.trans_lt hs
    exact ⟨by change 0 < halfTrace (reduced U i); unfold defect at hl; linarith,
      small_defect_chartRate _ hl⟩
  have hc := coercive_mod_gauge U
  linarith

private theorem halfweight_le_one (t : ℝ) (U : State) :
    Real.exp (-(1/t^2)*spatialAction U/2) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  have h := (spatial_action_bounds U).1
  have ht : 0 ≤ 1/t^2 := by positivity
  nlinarith

private theorem outside_halfweight (t : ℝ) (U : State) (hU : U ∉ region) :
    Real.exp (-(1/t^2)*spatialAction U/2) ≤ Real.exp (-(1/t^2)/32) := by
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (outside_energy U hU) (by positivity : 0 ≤ 1/t^2)
  nlinarith

theorem exponential_polynomial (t : ℝ) (ht : 0 < t) :
    Real.exp (-(1/t^2)/32) ≤ (40320*32^8)*t^16 := by
  let x : ℝ := (1/t^2)/32
  have hx : 0 < x := by dsimp [x]; positivity
  have hp := Real.pow_div_factorial_le_exp x hx.le 8
  have hm := mul_le_mul_of_nonneg_right hp (Real.exp_pos (-x)).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hm
  have hb : Real.exp (-x) ≤ 40320/x^8 := (le_div_iff₀ (pow_pos hx 8)).mpr (by norm_num at hm; nlinarith)
  have he : 40320/x^8=(40320*32^8)*t^16 := by
    dsimp [x]
    field_simp [ht.ne']
    <;> ring
  convert hb.trans_eq he using 1 <;> dsimp [x] <;> congr 1 <;> ring

theorem outside_kernel_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (U V : State)
    (h : U ∉ region ∨ V ∉ region) :
    kernel (1/t^2) U V/t^36 ≤ errorConstant*t := by
  have hw : Real.exp (-(1/t^2)*spatialAction U/2)*Real.exp (-(1/t^2)*spatialAction V/2) ≤
      Real.exp (-(1/t^2)/32) := by
    rcases h with hU | hV
    · have hm := mul_le_mul (outside_halfweight t U hU) (halfweight_le_one t V)
        (Real.exp_pos _).le (Real.exp_pos _).le
      simpa only [mul_one] using hm
    · have hm := mul_le_mul (halfweight_le_one t U) (outside_halfweight t V hV)
        (Real.exp_pos _).le (by norm_num : (0:ℝ)≤1)
      simpa only [one_mul] using hm
  have hk := CubeMatchedGround.kernel_upper t ht h1 U V
  have hC : 0 ≤ CubeMatchedGround.temporalConstant^7 := pow_nonneg CubeMatchedGround.temporalConstant_pos.le 7
  have hm := mul_le_mul_of_nonneg_right hw (mul_nonneg hC (pow_pos ht 21).le)
  have hp := mul_le_mul_of_nonneg_right (exponential_polynomial t ht) (mul_nonneg hC (pow_pos ht 21).le)
  have hm' : Real.exp (-(1/t^2)*spatialAction U/2)*Real.exp (-(1/t^2)*spatialAction V/2)*
      CubeMatchedGround.temporalConstant^7*t^21 ≤
      Real.exp (-(1/t^2)/32)*(CubeMatchedGround.temporalConstant^7*t^21) := by
    convert hm using 1 <;> ring
  apply (div_le_iff₀ (pow_pos ht 36)).mpr
  have hh : kernel (1/t^2) U V ≤
      ((40320*32^8)*t^16)*(CubeMatchedGround.temporalConstant^7*t^21) :=
    hk.trans (hm'.trans hp)
  convert hh using 1 <;> unfold errorConstant <;> ring

theorem discardedKernel_measurable (t : ℝ) : Measurable (discardedKernel t) :=
  ((kernel_joint_measurable (1/t^2)).div_const (t^36)).indicator
    (region_measurable.prod region_measurable).compl

theorem discardedKernel_nonnegative (t : ℝ) (ht : 0 < t) (p : State × State) :
    0 ≤ discardedKernel t p := by
  apply Set.indicator_nonneg
  intro p _
  exact div_nonneg (kernel_positive _ _ _).le (pow_pos ht 36).le

theorem discardedKernel_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (p : State × State) :
    discardedKernel t p ≤ errorConstant*t := by
  classical
  unfold discardedKernel
  by_cases hp : p ∈ (region ×ˢ region)ᶜ
  · rw [Set.indicator_of_mem hp]
    apply outside_kernel_bound t ht h1
    simpa only [Set.mem_compl_iff,Set.mem_prod,not_and_or] using hp
  · rw [Set.indicator_of_notMem hp]
    unfold errorConstant
    exact mul_nonneg (mul_nonneg (pow_nonneg CubeMatchedGround.temporalConstant_pos.le 7) (by norm_num)) ht.le

theorem discardedKernel_memLp (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    MemLp (discardedKernel t) 2 (boundaryHaar.prod boundaryHaar) := by
  apply MemLp.of_bound (discardedKernel_measurable t).aestronglyMeasurable (errorConstant*t)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (discardedKernel_nonnegative t ht p)]
  exact discardedKernel_bound t ht h1 p

/-- The discarded part vanishes in squared L2 on the ORIGINAL full boundary-Haar product,
already divided by t^36. This includes both off-diagonal chart-complement blocks. -/
theorem integral_sq_discarded_tendsto :
    Tendsto (fun t : ℝ => ∫ p : State × State, (discardedKernel t p)^2 ∂boundaryHaar.prod boundaryHaar)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hL : Tendsto (fun t : ℝ => (errorConstant*t)^2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => (errorConstant*t)^2) :=
      (continuous_const.mul continuous_id).pow 2
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) ?_ hL
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht h1
  have hi := (discardedKernel_memLp t ht h1).integrable_sq
  have h := integral_mono hi (integrable_const ((errorConstant*t)^2))
    (fun p => pow_le_pow_left₀ (discardedKernel_nonnegative t ht p) (discardedKernel_bound t ht h1 p) 2)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h

def normalizedDiscarded (t : ℝ) (d : CubeSlabGround.GroundData (1/t^2)) (p : State × State) : ℝ :=
  (t^36/d.value)*discardedKernel t p

theorem normalizedDiscarded_eq (t : ℝ) (ht : 0 < t)
    (d : CubeSlabGround.GroundData (1/t^2)) (p : State × State) :
    normalizedDiscarded t d p=
      (region ×ˢ region)ᶜ.indicator (fun p => kernel (1/t^2) p.1 p.2/d.value) p := by
  classical
  unfold normalizedDiscarded discardedKernel
  by_cases hp : p ∈ (region ×ˢ region)ᶜ
  · rw [Set.indicator_of_mem hp,Set.indicator_of_mem hp]
    field_simp [ht.ne']
  · rw [Set.indicator_of_notMem hp,Set.indicator_of_notMem hp,mul_zero]

theorem normalizedDiscarded_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (d : CubeSlabGround.GroundData (1/t^2)) (p : State × State) :
    normalizedDiscarded t d p ≤ (errorConstant/CubeRootGround.lowerConstant)*t := by
  have hv := (CubeMatchedGround.normalization_bounds t ht h1 d).1
  have hr : t^36/d.value ≤ 1/CubeRootGround.lowerConstant := by
    apply (div_le_div_iff₀ d.value_pos CubeRootGround.lowerConstant_pos).mpr
    simpa only [one_mul,mul_one,mul_comm] using hv
  have h := mul_le_mul hr (discardedKernel_bound t ht h1 p)
    (discardedKernel_nonnegative t ht p) (one_div_pos.mpr CubeRootGround.lowerConstant_pos).le
  unfold normalizedDiscarded
  convert h using 1 <;> ring

theorem normalizedDiscarded_memLp (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (d : CubeSlabGround.GroundData (1/t^2)) :
    MemLp (normalizedDiscarded t d) 2 (boundaryHaar.prod boundaryHaar) :=
  (discardedKernel_memLp t ht h1).const_mul (t^36/d.value)

/-- The actual K/lambda off-chart kernel vanishes for ANY supplied family of genuine
ground data, using the previously verified uniform lower normalization bound. -/
theorem integral_sq_normalized_tendsto (d : ∀ t : ℝ, CubeSlabGround.GroundData (1/t^2)) :
    Tendsto (fun t : ℝ => ∫ p : State × State, (normalizedDiscarded t (d t) p)^2
      ∂boundaryHaar.prod boundaryHaar) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hL : Tendsto (fun t : ℝ => ((errorConstant/CubeRootGround.lowerConstant)*t)^2)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => ((errorConstant/CubeRootGround.lowerConstant)*t)^2) :=
      (continuous_const.mul continuous_id).pow 2
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using
      (hc.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  apply squeeze_zero' (Eventually.of_forall (fun _ => integral_nonneg (fun _ => sq_nonneg _))) ?_ hL
  filter_upwards [self_mem_nhdsWithin,
    (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht h1
  have hn (p : State × State) : 0 ≤ normalizedDiscarded t (d t) p :=
    mul_nonneg (div_nonneg (pow_pos ht 36).le (d t).value_pos.le)
      (discardedKernel_nonnegative t ht p)
  have h := integral_mono (normalizedDiscarded_memLp t ht h1 (d t)).integrable_sq
    (integrable_const (((errorConstant/CubeRootGround.lowerConstant)*t)^2))
    (fun p => pow_le_pow_left₀ (hn p) (normalizedDiscarded_bound t ht h1 (d t) p) 2)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using h

end OperatorDerivativeRewrite.Foundation.CubeBoundaryExterior
