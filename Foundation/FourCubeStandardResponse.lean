import Foundation.FourCubeDirichletAffinity
/-! Direct native response in the actual standard864-face Dirichlet law.
The nonconstant interior completion stays in the measure throughout. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourCubeStandardResponse
open QuaternionSU2Representation FourCubeHaarParity FourCubeHaarContinuousIntegral
open FourCubeConditionalScore (actionDirection)
open FourCubeBoundarySmoothAction (action action_apply)
attribute [local irreducible] action haarIntegral OneSidedBlockIncidence.edges OneSidedBlockIncidence.upperFaces

def boundary (a : Parameters) : Fin 3 → SU2 := FourCubeCompletedHaar.angles (a 0) (a 1) (a 2)

def diagonal : Observables := ⟨FourCubeCompletedHaar.diagonal,by
  unfold FourCubeCompletedHaar.diagonal FourCubePinnedCoercivity.defect
  exact continuous_finset_sum _ (fun e _ => continuous_const.mul
    (continuous_const.sub (FourCubeBoundarySmoothAction.halfTrace_continuous.comp (continuous_apply e))))⟩

def energy (a : Parameters) : Observables := action a+diagonal

theorem energy_apply (a : Parameters) (s : InteriorState) :
    energy a s=FourCubeCompletedHaar.completedAction (boundary a) s := by
  have h1 := FourCubeExteriorSources.full_angle_identity (a 0) (a 1) (a 2) s
  have h2 := FourCubeCompletedHaar.action_split (boundary a) s
  rw [boundary,FourCubeCompletedHaar.sourceCost_angles] at h2
  change FourCubeDirichletBox.action (FourCubeCompletedHaar.angles (a 0) (a 1) (a 2)) s=_ at h1
  change action a s+FourCubeCompletedHaar.diagonal s=_
  rw [action_apply]
  unfold FourCubeCompletedHaar.diagonal at *
  unfold boundary
  linarith

theorem energy_bounds (a : Parameters) (s : InteriorState) : 0≤energy a s ∧ energy a s≤240 := by
  rw [energy_apply]
  exact ⟨FourCubeCompletedHaar.completed_nonneg _ _,FourCubeCompletedHaar.completed_upper _ _⟩

def penaltyWeight (β : ℝ) : Observables := NormedSpace.exp ((-β) • diagonal)
def weight (β : ℝ) (a : Parameters) : Observables := FourCubeConditionalScore.weight β a*penaltyWeight β

theorem weight_apply (β : ℝ) (a : Parameters) (s : InteriorState) :
    weight β a s=Real.exp (-β*energy a s) := by
  rw [weight,ContinuousMap.mul_apply,FourCubeConditionalScore.weight_apply,
    penaltyWeight,exp_apply]
  simp only [ContinuousMap.smul_apply,smul_eq_mul,← Real.exp_add]
  change Real.exp (-β*FourCubeIntegratedCubic.cellAction (a 0) (a 1) (a 2) s+-β*diagonal s)=_
  rw [energy,ContinuousMap.add_apply,action_apply]
  congr 1
  ring

def partition (β : ℝ) (a : Parameters) : ℝ := haarIntegral (weight β a)

theorem partition_eq_completed (β : ℝ) (a : Parameters) :
    partition β a=FourCubeCompletedHaar.completedPartition β (boundary a) := by
  rw [partition,haarIntegral_apply]
  apply integral_congr_ae
  filter_upwards with s
  rw [weight_apply,energy_apply]
  rfl

theorem partition_pos (β : ℝ) (a : Parameters) : 0<partition β a := by
  rw [partition_eq_completed]
  exact FourCubeCompletedHaar.completed_positive _ _

def expectation (β : ℝ) (a : Parameters) (f : Observables) : ℝ :=
  haarIntegral (f*weight β a)/partition β a

def law (β : ℝ) (a : Parameters) : Measure InteriorState := FourCubeScalarCalibration.standardLaw β (boundary a)

instance law_probability (β : ℝ) (a : Parameters) : IsProbabilityMeasure (law β a) :=
  FourCubeScalarCalibration.standardLaw_probability β _

theorem law_density (β : ℝ) (a : Parameters) :
    law β a=interiorHaar.withDensity (fun s => ENNReal.ofReal (weight β a s/partition β a)) := by
  unfold law FourCubeScalarCalibration.standardLaw
  congr 1
  funext s
  rw [FourCubeCompletedHaar.normalized_density,weight_apply,energy_apply,partition_eq_completed]
  rfl

theorem law_integral (β : ℝ) (a : Parameters) (f : Observables) :
    (∫ s,f s ∂law β a)=expectation β a f := by
  have hm : Measurable (fun s => weight β a s/partition β a) := (weight β a).continuous.measurable.div_const _
  have hn (s : InteriorState) : 0≤weight β a s/partition β a := by
    rw [weight_apply]
    exact div_nonneg (Real.exp_pos _).le (partition_pos β a).le
  rw [law_density,integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hn _),smul_eq_mul]
  rw [expectation,haarIntegral_apply,← integral_div]
  apply integral_congr_ae
  filter_upwards with s
  change weight β a s/partition β a*f s=(f s*weight β a s)/partition β a
  ring

theorem weight_hasDerivAt (β : ℝ) (a u : Parameters) :
    HasDerivAt (fun h : ℝ => weight β (a+h • u))
      (weight β a*((-β) • actionDirection a u)) 0 := by
  have h := (FourCubeConditionalScore.weight_hasDerivAt β a u).mul_const (penaltyWeight β)
  convert h using 1
  · rfl
  · ext s
    simp only [weight,ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
    ring

theorem weighted_hasDerivAt (β : ℝ) (a u : Parameters) (f : Observables) :
    HasDerivAt (fun h : ℝ => haarIntegral (f*weight β (a+h • u)))
      (-β*haarIntegral ((f*actionDirection a u)*weight β a)) 0 := by
  have h := haarIntegral.hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_const (0:ℝ) f).mul (weight_hasDerivAt β a u))
  convert h using 1
  · rfl
  · simp only [zero_mul,zero_add]
    rw [show f*(weight β a*((-β) • actionDirection a u))=
        (-β) • ((f*actionDirection a u)*weight β a) by
      ext s
      simp only [ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
      ring,map_smul]
    rfl

def response (β : ℝ) (a u : Parameters) (f : Observables) : ℝ :=
  -β*(expectation β a (f*actionDirection a u)-expectation β a f*expectation β a (actionDirection a u))

theorem expectation_hasDerivAt (β : ℝ) (a u : Parameters) (f : Observables) :
    HasDerivAt (fun h : ℝ => expectation β (a+h • u) f) (response β a u f) 0 := by
  have h1 := weighted_hasDerivAt β a u f
  have h0 := weighted_hasDerivAt β a u 1
  simp only [one_mul] at h0
  have hz : haarIntegral (weight β (a+(0:ℝ) • u))≠0 := by
    change partition β (a+(0:ℝ) • u)≠0
    simpa only [zero_smul,add_zero] using (partition_pos β a).ne'
  have h := h1.div h0 hz
  convert h using 1
  · rfl
  · unfold response expectation partition
    simp only [zero_smul,add_zero]
    have hz0 : haarIntegral (weight β a)≠0 := (partition_pos β a).ne'
    field_simp [hz0]
    <;> ring

def score (β : ℝ) (a u : Parameters) : Observables :=
  (-β) • (actionDirection a u-ContinuousMap.const _ (expectation β a (actionDirection a u)))
abbrev Native (β : ℝ) (a : Parameters) := Lp ℝ 2 (law β a)
def nativeScore (β : ℝ) (a u : Parameters) : Native β a := ContinuousMap.toLp 2 (law β a) ℝ (score β a u)
def nativeResponse (β : ℝ) (a u : Parameters) : Native β a →L[ℝ] ℝ := innerSL ℝ (nativeScore β a u)

theorem observable_integrable_native (β : ℝ) (a : Parameters) (f : Observables) :
    Integrable f (law β a) :=
  Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Eventually.of_forall (fun s => f.norm_coe_le_norm s))

theorem nativeResponse_core (β : ℝ) (a u : Parameters) (f : Observables) :
    nativeResponse β a u (ContinuousMap.toLp 2 (law β a) ℝ f)=response β a u f := by
  rw [nativeResponse,innerSL_apply_apply,nativeScore,ContinuousMap.inner_toLp]
  have he : (fun s => f s*starRingEnd ℝ (score β a u s))=
      (fun s => -β*((f*actionDirection a u) s-f s*expectation β a (actionDirection a u))) := by
    funext s
    simp only [starRingEnd_apply,star_trivial,score,ContinuousMap.smul_apply,
      ContinuousMap.sub_apply,ContinuousMap.const_apply,ContinuousMap.mul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul,integral_sub (observable_integrable_native β a (f*actionDirection a u))
      ((observable_integrable_native β a f).mul_const _),integral_mul_const,law_integral,law_integral]
  rfl

theorem native_derivative (β : ℝ) (a u : Parameters) (f : Observables) :
    HasDerivAt (fun h : ℝ => ∫ s,f s ∂law β (a+h • u))
      (nativeResponse β a u (ContinuousMap.toLp 2 (law β a) ℝ f)) 0 := by
  simp_rw [law_integral,nativeResponse_core]
  exact expectation_hasDerivAt β a u f

theorem nativeResponse_norm (β : ℝ) (a u : Parameters) : ‖nativeResponse β a u‖=‖nativeScore β a u‖ :=
  innerSL_apply_norm ℝ (nativeScore β a u)

theorem nativeScore_norm_square (β : ℝ) (a u : Parameters) :
    ‖nativeScore β a u‖^2=β^2*ProbabilityTheory.variance (actionDirection a u) (law β a) := by
  rw [← real_inner_self_eq_norm_sq,nativeScore,ContinuousMap.inner_toLp]
  have hv := ProbabilityTheory.variance_eq_integral
    (μ := law β a) (actionDirection a u).continuous.measurable.aemeasurable
  rw [law_integral] at hv
  rw [hv,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  simp only [starRingEnd_apply,star_trivial,score,ContinuousMap.smul_apply,
    ContinuousMap.sub_apply,ContinuousMap.const_apply,smul_eq_mul]
  ring

private theorem axis_zero (j : Fin 3) : SU2JointPlaquetteCubic.axis j 0=1 := by
  apply Subtype.ext
  change (SU2JointPlaquetteCubic.axis j 0 : SU2TraceHessianModel.M2)=1
  rw [SU2AxisMatrixJets.axis_matrix_formula]
  simp

private theorem boundary_zero : FourCubeIntegratedCubic.boundaryData 0 0 0=fun _ => (1:SU2) := by
  funext c
  cases c <;> simp [FourCubeIntegratedCubic.boundaryData,axis_zero]

private theorem action_zero (s : InteriorState) : action 0 s=FourCubePinnedCoercivity.vacuumAction s := by
  rw [action_apply]
  change FourCubeBoundaryCubic.fullAction (FourCubeIntegratedCubic.fill
    (FourCubeIntegratedCubic.boundaryData 0 0 0) s)=_
  rw [boundary_zero]
  rfl

theorem diagonal_nonneg (s : InteriorState) : 0≤diagonal s :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (Nat.cast_nonneg _) (FourCubePinnedCoercivity.defect_nonneg _))

/-- Full32 comparison: the nonnegative interior penalty is RETAINED on both sides. -/
theorem energy_comparison (a : Parameters) (s : InteriorState) :
    energy a s≤3*energy 0 s+3*FourCubeBoundaryCoercivity.boundaryCost
      (FourCubeIntegratedCubic.boundaryData (a 0) (a 1) (a 2)) ∧
    energy 0 s/3-FourCubeBoundaryCoercivity.boundaryCost
      (FourCubeIntegratedCubic.boundaryData (a 0) (a 1) (a 2))≤energy a s := by
  have hu := FourCubeBoundaryCoercivity.boundaryAction_upper
    (FourCubeIntegratedCubic.boundaryData (a 0) (a 1) (a 2)) s
  have hl := FourCubeBoundaryCoercivity.boundaryAction_lower
    (FourCubeIntegratedCubic.boundaryData (a 0) (a 1) (a 2)) s
  change FourCubeIntegratedCubic.cellAction (a 0) (a 1) (a 2) s≤_ at hu
  change _≤FourCubeIntegratedCubic.cellAction (a 0) (a 1) (a 2) s at hl
  rw [← action_apply,← action_zero] at hu hl
  change action a s+diagonal s≤3*(action 0 s+diagonal s)+_ ∧
    (action 0 s+diagonal s)/3-_≤action a s+diagonal s
  constructor <;> linarith [diagonal_nonneg s]

theorem partition_upper (β : ℝ) (hβ : 0≤β) (a : Parameters) :
    partition β a≤Real.exp (β*FourCubeBoundaryCoercivity.boundaryCost
      (FourCubeIntegratedCubic.boundaryData (a 0) (a 1) (a 2)))*partition (β/3) 0 := by
  rw [partition,partition,haarIntegral_apply,haarIntegral_apply,← integral_const_mul]
  apply integral_mono (observable_integrable _) ((observable_integrable _).const_mul _)
  intro s
  simp only [weight_apply]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (energy_comparison a s).2 hβ
  nlinarith

theorem partition_lower (β : ℝ) (hβ : 0≤β) (a : Parameters) :
    Real.exp (-3*β*FourCubeBoundaryCoercivity.boundaryCost
      (FourCubeIntegratedCubic.boundaryData (a 0) (a 1) (a 2)))*partition (3*β) 0≤partition β a := by
  rw [partition,partition,haarIntegral_apply,haarIntegral_apply,← integral_const_mul]
  apply integral_mono ((observable_integrable _).const_mul _) (observable_integrable _)
  intro s
  simp only [weight_apply]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (energy_comparison a s).1 hβ
  nlinarith

theorem reference_partition (β : ℝ) : partition β 0=FourCubeDirichletAffinity.boxZ β := by
  rw [partition_eq_completed,FourCubeDirichletAffinity.boxZ_eq_completed]
  rfl

def actionExponential (β : ℝ) (a : Parameters) : Observables := NormedSpace.exp (((2:ℝ)/3*β) • energy a)

theorem exponential_partition (β : ℝ) (a : Parameters) :
    expectation β a (actionExponential β a)=partition (β/3) a/partition β a := by
  unfold expectation
  congr 1
  unfold partition
  congr 1
  ext s
  rw [ContinuousMap.mul_apply,weight_apply,weight_apply,actionExponential,exp_apply]
  simp only [ContinuousMap.smul_apply,smul_eq_mul,← Real.exp_add]
  congr 1
  ring

theorem scaled_action_mean (β : ℝ) (a : Parameters) :
    β*expectation β a (energy a)≤(3:ℝ)/2*expectation β a (actionExponential β a) := by
  have hp (s : InteriorState) : β*energy a s≤(3:ℝ)/2*actionExponential β a s := by
    have h := Real.add_one_le_exp ((2:ℝ)/3*β*energy a s)
    simp only [actionExponential,exp_apply,ContinuousMap.smul_apply,smul_eq_mul]
    linarith
  have h := integral_mono ((observable_integrable_native β a (energy a)).const_mul β)
    ((observable_integrable_native β a (actionExponential β a)).const_mul ((3:ℝ)/2)) hp
  rw [integral_const_mul,integral_const_mul,law_integral,law_integral] at h
  exact h

def partitionRatio (t : ℝ) : ℝ :=
  FourCubeDirichletAffinity.boxZ ((1/9)/t^2)/FourCubeDirichletAffinity.boxZ (3/t^2)

theorem partitionRatio_tendsto : Tendsto partitionRatio (𝓝[≠] 0)
    (𝓝 ((FourCubeDirichletAffinity.boxLimit*(Real.sqrt (1/9))⁻¹^96)/
      (FourCubeDirichletAffinity.boxLimit*(Real.sqrt (3:ℝ))⁻¹^96))) := by
  have h := (FourCubeDirichletAffinity.box_scaled_asymptotic (1/9) (by norm_num)).div
    (FourCubeDirichletAffinity.box_scaled_asymptotic 3 (by norm_num))
    (mul_pos FourCubeDirichletAffinity.boxLimit_pos (by positivity)).ne'
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change (FourCubeDirichletAffinity.boxZ ((1/9)/t^2)/|t|^96)/
    (FourCubeDirichletAffinity.boxZ (3/t^2)/|t|^96)=partitionRatio t
  unfold partitionRatio
  field_simp [(FourCubeDirichletAffinity.boxZ_pos (3/t^2)).ne',abs_ne_zero.mpr ht]

/-- The exponential-moment comparison now uses the ACTUAL96-dimensional box normalizer. -/
theorem moving_exponential_bound (t : ℝ) (ht : t≠0) (x y z R : ℝ)
    (hR : x^2+y^2+z^2≤R) :
    expectation (1/t^2) ![t*x,t*y,t*z] (actionExponential (1/t^2) ![t*x,t*y,t*z])≤
      Real.exp (720*R)*partitionRatio t := by
  let β : ℝ := 1/t^2
  let a : Parameters := ![t*x,t*y,t*z]
  let b := FourCubeScaledBoundaryControl.movingBoundary t x y z
  have hβ : 0≤β := by positivity
  have hb : β*FourCubeBoundaryCoercivity.boundaryCost b≤216*R :=
    (FourCubeScaledBoundaryControl.scaled_boundaryCost β t hβ (by dsimp [β]; field_simp) x y z).trans
      (by nlinarith)
  have hn := partition_upper (β/3) (by positivity) a
  have hd := partition_lower β hβ a
  have hn' : partition (β/3) a≤Real.exp (72*R)*FourCubeDirichletAffinity.boxZ ((1/9)/t^2) := by
    apply hn.trans
    change Real.exp ((β/3)*FourCubeBoundaryCoercivity.boundaryCost b)*partition ((β/3)/3) 0≤_
    rw [reference_partition]
    have he : (β/3)*FourCubeBoundaryCoercivity.boundaryCost b≤72*R := by linarith
    have h := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he)
      (FourCubeDirichletAffinity.boxZ_pos ((β/3)/3)).le
    convert h using 1 <;> dsimp [β] <;> congr 1 <;> ring
  have hd' : Real.exp (-648*R)*FourCubeDirichletAffinity.boxZ (3/t^2)≤partition β a := by
    apply le_trans _ hd
    change _≤Real.exp (-3*β*FourCubeBoundaryCoercivity.boundaryCost b)*partition (3*β) 0
    rw [reference_partition]
    have he : -648*R≤-3*β*FourCubeBoundaryCoercivity.boundaryCost b := by linarith
    have h := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) (FourCubeDirichletAffinity.boxZ_pos (3*β)).le
    convert h using 1 <;> dsimp [β] <;> congr 1 <;> ring
  rw [exponential_partition]
  change partition (β/3) a/partition β a≤_
  have hnr := div_le_div_of_nonneg_right hn' (partition_pos β a).le
  have hdr := div_le_div_of_nonneg_left
    (mul_nonneg (Real.exp_pos (72*R)).le (FourCubeDirichletAffinity.boxZ_pos ((1/9)/t^2)).le)
    (mul_pos (Real.exp_pos (-648*R)) (FourCubeDirichletAffinity.boxZ_pos (3/t^2))) hd'
  apply (hnr.trans hdr).trans_eq
  unfold partitionRatio
  rw [mul_div_mul_comm,← Real.exp_sub]
  congr 1
  congr 1
  ring

theorem uniform_scaled_action (R : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x y z : ℝ,x^2+y^2+z^2≤R →
      (1/t^2)*expectation (1/t^2) ![t*x,t*y,t*z] (energy ![t*x,t*y,t*z])≤C := by
  let L := (FourCubeDirichletAffinity.boxLimit*(Real.sqrt (1/9:ℝ))⁻¹^96)/
    (FourCubeDirichletAffinity.boxLimit*(Real.sqrt (3:ℝ))⁻¹^96)
  have hL : 0<L := by
    dsimp [L]
    apply div_pos
    · exact mul_pos FourCubeDirichletAffinity.boxLimit_pos (by positivity)
    · exact mul_pos FourCubeDirichletAffinity.boxLimit_pos (by positivity)
  refine ⟨(3:ℝ)/2*Real.exp (720*R)*(L+1),by positivity,?_⟩
  have he := partitionRatio_tendsto.eventually (eventually_lt_nhds (show L<L+1 by linarith))
  filter_upwards [he,self_mem_nhdsWithin] with t ht htn x y z hR
  have h := scaled_action_mean (1/t^2) (![t*x,t*y,t*z]:Parameters)
  have hb := moving_exponential_bound t htn x y z R hR
  have hm := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤3/2)
  have hf := mul_le_mul_of_nonneg_left ht.le (by positivity : 0≤(3:ℝ)/2*Real.exp (720*R))
  nlinarith only [h,hm,hf]

/-- The original exact SU2 derivative controls the retained, NONNEGATIVE completed energy. -/
theorem middle_gradient_bound (a : Parameters) (s : InteriorState) :
    (actionDirection a (FourCubeMixedMeanValue.basis 1) s)^2≤2*energy a s := by
  have h := FourCubeThermalScore.middle_gradient_bound (a 0) (a 1) (a 2) s
  have ha : (![a 0,a 1,a 2]:Parameters)=a := by
    ext j
    fin_cases j <;> rfl
  rw [ha,← action_apply a s] at h
  change (actionDirection a (FourCubeMixedMeanValue.basis 1) s)^2≤2*(action a s+diagonal s)
  linarith [diagonal_nonneg s]

theorem middle_thermal_score_bound (t : ℝ) (ht : t≠0) (x y z : ℝ) :
    ‖nativeScore (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)‖^2≤
      2*(1/t^2)*expectation (1/t^2) ![t*x,t*y,t*z] (energy ![t*x,t*y,t*z]) := by
  let β : ℝ := 1/t^2
  let a : Parameters := ![t*x,t*y,t*z]
  let D := actionDirection a (t • FourCubeMixedMeanValue.basis 1)
  have hd (s : InteriorState) : D s=t*actionDirection a (FourCubeMixedMeanValue.basis 1) s := by
    simp only [D,FourCubeConditionalScore.actionDirection,map_smul,ContinuousMap.smul_apply,smul_eq_mul]
  have hi : Integrable (fun s => (D s)^2) (law β a) := by
    have hi0 := observable_integrable_native β a (D*D)
    change Integrable (fun s => D s*D s) (law β a) at hi0
    simpa only [pow_two] using hi0
  have hp (s : InteriorState) : (D s)^2≤(2*t^2)*energy a s := by
    have h := mul_le_mul_of_nonneg_left (middle_gradient_bound a s) (sq_nonneg t)
    rw [hd,mul_pow]
    convert h using 1 <;> ring
  have hh := integral_mono hi ((observable_integrable_native β a (energy a)).const_mul (2*t^2)) hp
  rw [integral_const_mul,law_integral] at hh
  have hv := ProbabilityTheory.variance_le_expectation_sq (μ := law β a)
    (X := (D : InteriorState → ℝ)) D.continuous.measurable.aestronglyMeasurable
  simp only [Pi.pow_apply] at hv
  have he := mul_le_mul_of_nonneg_left (hv.trans hh) (sq_nonneg β)
  rw [nativeScore_norm_square]
  change β^2*ProbabilityTheory.variance D (law β a)≤2*β*expectation β a (energy a)
  have hclock : β*t^2=1 := by dsimp [β]; field_simp
  have halgebra : β^2*((2*t^2)*expectation β a (energy a))=2*β*expectation β a (energy a) := by
    calc
      _ = 2*β*(β*t^2)*expectation β a (energy a) := by ring
      _ = _ := by rw [hclock,mul_one]
  exact he.trans_eq halgebra

/-- Original native norm for the ACTUAL STANDARD864-face conditional law.
No small-density comparison with the cap law is used. -/
theorem uniform_middle_response (R : ℝ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x y z : ℝ,x^2+y^2+z^2≤R →
      ‖nativeResponse (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)‖^2≤C := by
  obtain ⟨C,hC,hbound⟩ := uniform_scaled_action R
  refine ⟨2*C,by positivity,?_⟩
  filter_upwards [hbound,self_mem_nhdsWithin] with t hb ht x y z hR
  rw [nativeResponse_norm]
  exact (middle_thermal_score_bound t ht x y z).trans
    (by have h := mul_le_mul_of_nonneg_left (hb x y z hR) (by norm_num : (0:ℝ)≤2); nlinarith only [h])

theorem amplitude_derivative (t x y z : ℝ) (f : Observables) :
    HasDerivAt (fun h : ℝ => ∫ s,f s ∂law (1/t^2) ![t*x,t*(y+h),t*z])
      (nativeResponse (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)
        (ContinuousMap.toLp 2 (law (1/t^2) ![t*x,t*y,t*z]) ℝ f)) 0 := by
  have he (h : ℝ) : (![t*x,t*y,t*z]:Parameters)+h • (t • FourCubeMixedMeanValue.basis 1)=
      ![t*x,t*(y+h),t*z] := by
    ext j
    fin_cases j <;> simp [FourCubeMixedMeanValue.basis,Pi.single_apply] <;> ring
  simpa only [he] using native_derivative (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1) f
end OperatorDerivativeRewrite.Foundation.FourCubeStandardResponse
