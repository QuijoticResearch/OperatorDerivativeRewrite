import Foundation.FourCubeConditionalScore
import Foundation.FourCubeMovingBoundaryConcentration
import Foundation.FourCubeMixedMeanValue
/-! Thermal normalization for the actual all32 Wilson conditional score.
The estimates retain actual partition functions and original native L2 norms.
No contraction constant, uniform-volume estimate or physical distance scale is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Quaternion
namespace OperatorDerivativeRewrite.Foundation.FourCubeThermalScore
open FourCubeConditionalScore FourCubeHaarContinuousIntegral FourCubeBoundarySmoothAction
open FourCubeHaarParity FourCubeIntegratedCubic FourCubePinnedHaar FourCubePinnedConcentration
open FourCubeBoundaryCoercivity FourCubeScaledBoundaryControl
attribute [local irreducible] action haarIntegral OneSidedBlockIncidence.edges OneSidedBlockIncidence.upperFaces

def actionExponential (β : ℝ) (a : Parameters) : Observables :=
  NormedSpace.exp (((2:ℝ)/3*β) • action a)

theorem exponential_partition (β : ℝ) (a : Parameters) :
    expectation β a (actionExponential β a)=
      FourCubeBoundarySmoothPartition.partition (β/3) a/FourCubeBoundarySmoothPartition.partition β a := by
  unfold expectation
  congr 1
  unfold FourCubeBoundarySmoothPartition.partition
  congr 1
  ext s
  simp only [actionExponential,FourCubeConditionalScore.weight,ContinuousMap.mul_apply,exp_apply,
    ContinuousMap.smul_apply,smul_eq_mul,← Real.exp_add]
  congr 1
  ring

theorem scaled_action_mean (β : ℝ) (a : Parameters) :
    β*expectation β a (action a)≤(3:ℝ)/2*expectation β a (actionExponential β a) := by
  have hpoint (s : InteriorState) : β*action a s≤(3:ℝ)/2*actionExponential β a s := by
    have h := Real.add_one_le_exp ((2:ℝ)/3*β*action a s)
    simp only [actionExponential,exp_apply,ContinuousMap.smul_apply,smul_eq_mul]
    linarith
  have h := integral_mono ((observable_integrable_native β a (action a)).const_mul β)
    ((observable_integrable_native β a (actionExponential β a)).const_mul ((3:ℝ)/2)) hpoint
  rw [integral_const_mul,integral_const_mul,law_integral,law_integral] at h
  exact h

def partitionRatio (t : ℝ) : ℝ := normalizer ((1/9)/t^2)/normalizer (3/t^2)

theorem partitionRatio_tendsto : Tendsto partitionRatio (𝓝[≠] 0)
    (𝓝 (((Real.sqrt (1/9))⁻¹^93)/((Real.sqrt (3:ℝ))⁻¹^93))) := by
  have h := (FourCubePhysicalEnergy.partition_ratio_tendsto (1/9) (by norm_num)).div
    (FourCubePhysicalEnergy.partition_ratio_tendsto 3 (by norm_num)) (by positivity)
  apply h.congr'
  filter_upwards with t
  change (normalizer ((1/9)/t^2)/normalizer (1/t^2))/(normalizer (3/t^2)/normalizer (1/t^2))=
    normalizer ((1/9)/t^2)/normalizer (3/t^2)
  field_simp [(normalizer_positive (1/t^2)).ne',(normalizer_positive (3/t^2)).ne']
  exact mul_div_cancel_right₀ _ (normalizer_positive _).ne'

theorem moving_exponential_bound (t : ℝ) (ht : t≠0) (x y z R : ℝ)
    (hR : x^2+y^2+z^2≤R) :
    expectation (1/t^2) ![t*x,t*y,t*z] (actionExponential (1/t^2) ![t*x,t*y,t*z])≤
      Real.exp (720*R)*partitionRatio t := by
  let β : ℝ := 1/t^2
  let b := movingBoundary t x y z
  have hβ : 0≤β := by positivity
  have hb : β*boundaryCost b≤216*R :=
    (scaled_boundaryCost β t hβ (by dsimp [β]; field_simp) x y z).trans (by nlinarith)
  have hn := pinnedPartition_upper (β/3) (by positivity) b
  have hd := pinnedPartition_lower β hβ b
  have hn' : pinnedPartition (β/3) b≤Real.exp (72*R)*normalizer ((1/9)/t^2) := by
    apply hn.trans
    have he : (β/3)*boundaryCost b≤72*R := by linarith
    have ha := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
      (normalizer_positive ((β/3)/3)).le
    convert ha using 1 <;> dsimp [β] <;> congr 1 <;> ring
  have hd' : Real.exp (-648*R)*normalizer (3/t^2)≤pinnedPartition β b := by
    apply le_trans _ hd
    have he : -648*R≤-3*β*boundaryCost b := by linarith
    have ha := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (normalizer_positive (3*β)).le
    convert ha using 1 <;> dsimp [β] <;> congr 1 <;> ring
  rw [exponential_partition,FourCubeBoundarySmoothPartition.partition_eq_actual,
    FourCubeBoundarySmoothPartition.partition_eq_actual,partition3_eq_pinned,partition3_eq_pinned]
  change pinnedPartition (β/3) b/pinnedPartition β b≤_
  have hnr := div_le_div_of_nonneg_right hn' (pinnedPartition_positive β b).le
  have hdr := div_le_div_of_nonneg_left
    (mul_nonneg (Real.exp_pos (72*R)).le (normalizer_positive ((1/9)/t^2)).le)
    (mul_pos (Real.exp_pos (-648*R)) (normalizer_positive (3/t^2))) hd'
  have hr := hnr.trans hdr
  apply hr.trans_eq
  unfold partitionRatio
  rw [mul_div_mul_comm,← Real.exp_sub]
  congr 1
  congr 1
  ring

/-- One punctured neighborhood controls all boundary amplitudes in the stated ball. -/
theorem uniform_scaled_action (R : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x y z : ℝ,x^2+y^2+z^2≤R →
      (1/t^2)*expectation (1/t^2) ![t*x,t*y,t*z] (action ![t*x,t*y,t*z])≤C := by
  let L := ((Real.sqrt (1/9:ℝ))⁻¹^93)/((Real.sqrt (3:ℝ))⁻¹^93)
  have hL : 0<L := by dsimp [L]; positivity
  refine ⟨(3:ℝ)/2*Real.exp (720*R)*(L+1),by positivity,?_⟩
  have he := partitionRatio_tendsto.eventually (eventually_lt_nhds (show L<L+1 by linarith))
  filter_upwards [he,self_mem_nhdsWithin] with t ht htn x y z hR
  have h := scaled_action_mean (1/t^2) (![t*x,t*y,t*z]:Parameters)
  have hb := moving_exponential_bound t htn x y z R hR
  have hm := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤3/2)
  have hf := mul_le_mul_of_nonneg_left ht.le (by positivity : 0≤(3:ℝ)/2*Real.exp (720*R))
  exact h.trans (hm.trans (by nlinarith only [hf]))

open QuaternionSU2Representation FourCubeHaarChannels

/-- Exact one-angle trace derivative control in the real SU2 group, not an ambient norm proxy. -/
theorem one_axis_control (B : SU2) (y : ℝ) :
    DifferentiableAt ℝ (fun r => halfTrace (SU2JointPlaquetteCubic.axis 1 r*B)) y ∧
      (deriv (fun r => halfTrace (SU2JointPlaquetteCubic.axis 1 r*B)) y)^2≤
        2*(1-halfTrace (SU2JointPlaquetteCubic.axis 1 y*B)) := by
  obtain ⟨q,rfl⟩ := hom_surjective B
  have he (r : ℝ) : halfTrace (SU2JointPlaquetteCubic.axis 1 r*hom q)=
      Real.cos r*(q:ℍ).re-Real.sin r*(q:ℍ).imJ := by
    rw [SU2JointPlaquetteCubic.axis,← hom.map_mul,halfTrace_map]
    change (SU2JointPlaquetteCubic.axisRaw 1 r*(q:ℍ)).re=_
    simp [SU2JointPlaquetteCubic.axisRaw,Quaternion.re_mul,sub_eq_add_neg]
  have hd : HasDerivAt (fun r => halfTrace (SU2JointPlaquetteCubic.axis 1 r*hom q))
      (-Real.sin y*(q:ℍ).re-Real.cos y*(q:ℍ).imJ) y := by
    simp_rw [he]
    exact ((Real.hasDerivAt_cos y).mul_const _).sub ((Real.hasDerivAt_sin y).mul_const _)
  refine ⟨hd.differentiableAt,?_⟩
  have hn : Quaternion.normSq (q:ℍ)=1 := by
    rw [Quaternion.normSq_eq_norm_mul_self,CStarRing.norm_coe_unitary,one_mul]
  rw [Quaternion.normSq_def'] at hn
  have hc : (q:ℍ).re^2+(q:ℍ).imJ^2≤1 := by
    nlinarith [sq_nonneg (q:ℍ).imI,sq_nonneg (q:ℍ).imK]
  have hs : (-Real.sin y*(q:ℍ).re-Real.cos y*(q:ℍ).imJ)^2+
      (Real.cos y*(q:ℍ).re-Real.sin y*(q:ℍ).imJ)^2=(q:ℍ).re^2+(q:ℍ).imJ^2 := by
    calc
      _ = (Real.sin y^2+Real.cos y^2)*((q:ℍ).re^2+(q:ℍ).imJ^2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq,one_mul]
  rw [hd.deriv,he]
  nlinarith [sq_nonneg (1-(Real.cos y*(q:ℍ).re-Real.sin y*(q:ℍ).imJ))]

private theorem internal_nonnegative (s : InteriorState) : 0 ≤ internalAction s := by
  unfold internalAction FourCubeWilsonCubic.innerAction
  apply Finset.sum_nonneg
  intro p _
  exact FourCubePinnedCoercivity.defect_nonneg _

private theorem component_le {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i,0≤f i) (i : ι) : f i≤∑ j,f j :=
  Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)

theorem ribbon_defect_le_action (x y z : ℝ) (s : InteriorState) :
    1-halfTrace (SU2JointPlaquetteCubic.axis 0 x*SU2JointPlaquetteCubic.axis 1 y*
      SU2JointPlaquetteCubic.axis 2 z*s chosenEdge)≤cellAction x y z s := by
  let b := boundaryData x y z
  calc
    _ = FourCubePinnedCoercivity.defect (s (OneSidedCapComplex.ribbonInterior chosen)*word b chosen) := by
      rw [chosen_edge,word_chosen]
      unfold FourCubePinnedCoercivity.defect
      rw [SU2WilsonConvolution.halfTrace_mul_comm]
    _ ≤ ∑ p : OneSidedBlockRank.Upper,FourCubePinnedCoercivity.defect
        (s (OneSidedCapComplex.ribbonInterior p)*word b p) :=
      component_le (ι := OneSidedBlockRank.Upper)
        (fun p => FourCubePinnedCoercivity.defect (s (OneSidedCapComplex.ribbonInterior p)*word b p))
        (fun p => FourCubePinnedCoercivity.defect_nonneg _) chosen
    _ ≤ boundaryAction b s := by
      rw [boundaryAction_decomposition]
      linarith [internal_nonnegative s]
    _ = _ := rfl

theorem middle_gradient_bound (x y z : ℝ) (s : InteriorState) :
    (actionDirection ![x,y,z] (FourCubeMixedMeanValue.basis 1) s)^2≤2*cellAction x y z s := by
  let B := SU2JointPlaquetteCubic.axis 2 z*s chosenEdge*SU2JointPlaquetteCubic.axis 0 x
  have he (r : ℝ) : halfTrace (SU2JointPlaquetteCubic.axis 0 x*SU2JointPlaquetteCubic.axis 1 r*
      SU2JointPlaquetteCubic.axis 2 z*s chosenEdge)=halfTrace (SU2JointPlaquetteCubic.axis 1 r*B) := by
    calc
      _ = halfTrace (SU2JointPlaquetteCubic.axis 0 x*
          (SU2JointPlaquetteCubic.axis 1 r*SU2JointPlaquetteCubic.axis 2 z*s chosenEdge)) := by congr 1; group
      _ = halfTrace ((SU2JointPlaquetteCubic.axis 1 r*SU2JointPlaquetteCubic.axis 2 z*s chosenEdge)*
          SU2JointPlaquetteCubic.axis 0 x) := SU2WilsonConvolution.halfTrace_mul_comm _ _
      _ = _ := by congr 1; dsimp [B]; group
  have hl : HasDerivAt (fun r : ℝ => (![x,r,z]:Parameters)) (FourCubeMixedMeanValue.basis 1) y := by
    apply hasDerivAt_pi.mpr
    intro j
    fin_cases j
    · simpa [FourCubeMixedMeanValue.basis,Pi.single_apply] using hasDerivAt_const y x
    · convert! hasDerivAt_id y using 1 <;> simp [FourCubeMixedMeanValue.basis,Pi.single_apply]
    · simpa [FourCubeMixedMeanValue.basis,Pi.single_apply] using hasDerivAt_const y z
  have hA := (action_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt y hl
  have hE := (ContinuousMap.evalCLM ℝ s).hasFDerivAt.comp_hasDerivAt y hA
  have hp : HasDerivAt (fun r => cellAction x r z s)
      (actionDirection ![x,y,z] (FourCubeMixedMeanValue.basis 1) s) y := by
    convert! hE using 1 <;>
      simp only [Function.comp_def,ContinuousMap.evalCLM_apply,action_apply,actionDirection,
        Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] <;> rfl
  have hf : (fun r => cellAction x r z s)=
      (fun r => residualAction x z s-halfTrace (SU2JointPlaquetteCubic.axis 1 r*B)) := by
    funext r
    rw [cellAction_residual]
    exact congrArg (fun q : ℝ => residualAction x z s-q) (he r)
  rw [hf] at hp
  have hc := one_axis_control B y
  have hd := (hasDerivAt_const y (residualAction x z s)).sub hc.1.hasDerivAt
  have hq := hp.unique hd
  have hb : (actionDirection ![x,y,z] (FourCubeMixedMeanValue.basis 1) s)^2≤
      2*(1-halfTrace (SU2JointPlaquetteCubic.axis 0 x*SU2JointPlaquetteCubic.axis 1 y*
        SU2JointPlaquetteCubic.axis 2 z*s chosenEdge)) := by
    rw [hq,he]
    simpa only [zero_sub,neg_sq] using hc.2
  exact hb.trans (mul_le_mul_of_nonneg_left (ribbon_defect_le_action x y z s) (by norm_num))

/-- Native score control at the established Gaussian angular normalization, retaining the true law. -/
theorem middle_thermal_score_bound (t : ℝ) (ht : t≠0) (x y z : ℝ) :
    ‖nativeScore (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)‖^2≤
      2*(1/t^2)*expectation (1/t^2) ![t*x,t*y,t*z] (action ![t*x,t*y,t*z]) := by
  let β : ℝ := 1/t^2
  let a : Parameters := ![t*x,t*y,t*z]
  let D := actionDirection a (t • FourCubeMixedMeanValue.basis 1)
  have hd (s : InteriorState) : D s=t*actionDirection a (FourCubeMixedMeanValue.basis 1) s := by
    simp only [D,actionDirection,map_smul,ContinuousMap.smul_apply,smul_eq_mul]
  have hi : Integrable (fun s => (D s)^2) (law β a) := by
    have hi0 := observable_integrable_native β a (D*D)
    change Integrable (fun s => D s*D s) (law β a) at hi0
    simpa only [pow_two] using hi0
  have hp (s : InteriorState) : (D s)^2≤(2*t^2)*action a s := by
    have h := mul_le_mul_of_nonneg_left (middle_gradient_bound (t*x) (t*y) (t*z) s) (sq_nonneg t)
    rw [hd,mul_pow,action_apply]
    change t^2*(actionDirection ![t*x,t*y,t*z] (FourCubeMixedMeanValue.basis 1) s)^2≤
      2*t^2*cellAction (t*x) (t*y) (t*z) s
    convert h using 1 <;> ring
  have hh := integral_mono hi ((observable_integrable_native β a (action a)).const_mul (2*t^2)) hp
  rw [integral_const_mul,law_integral] at hh
  have hv := ProbabilityTheory.variance_le_expectation_sq (μ := law β a)
    (X := (D : InteriorState → ℝ)) D.continuous.measurable.aestronglyMeasurable
  simp only [Pi.pow_apply] at hv
  have he := mul_le_mul_of_nonneg_left (hv.trans hh) (sq_nonneg β)
  rw [nativeScore_norm_square]
  change β^2*ProbabilityTheory.variance D (law β a)≤2*β*expectation β a (action a)
  have hclock : β*t^2=1 := by dsimp [β]; field_simp
  have halgebra : β^2*((2*t^2)*expectation β a (action a))=2*β*expectation β a (action a) := by
    calc
      _ = 2*β*(β*t^2)*expectation β a (action a) := by ring
      _ = _ := by rw [hclock,mul_one]
  exact he.trans_eq halgebra

/-- Uniform in every amplitude in a fixed ball and on a common punctured neighborhood.
The constant need not be below one and has no uniform-volume interpretation. -/
theorem uniform_middle_response (R : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x y z : ℝ,x^2+y^2+z^2≤R →
      ‖nativeResponse (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)‖^2≤C := by
  obtain ⟨C,hC,hbound⟩ := uniform_scaled_action R
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hbound,self_mem_nhdsWithin] with t hb ht x y z hR
  rw [nativeResponse_norm]
  exact (middle_thermal_score_bound t ht x y z).trans
    (by have h := mul_le_mul_of_nonneg_left (hb x y z hR) (by norm_num : (0:ℝ)≤2); nlinarith only [h])

/-- The controlled functional is the ACTUAL derivative in the rescaled middle boundary amplitude. -/
theorem amplitude_derivative (t x y z : ℝ) (f : Observables) :
    HasDerivAt (fun h : ℝ => ∫ s,f s ∂law (1/t^2) ![t*x,t*(y+h),t*z])
      (nativeResponse (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)
        (ContinuousMap.toLp 2 (law (1/t^2) ![t*x,t*y,t*z]) ℝ f)) 0 := by
  have he (h : ℝ) : (![t*x,t*y,t*z]:Parameters)+h • (t • FourCubeMixedMeanValue.basis 1)=
      ![t*x,t*(y+h),t*z] := by
    ext j
    fin_cases j <;> simp [FourCubeMixedMeanValue.basis,Pi.single_apply] <;> ring
  simpa only [he] using native_derivative (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1) f
end OperatorDerivativeRewrite.Foundation.FourCubeThermalScore
