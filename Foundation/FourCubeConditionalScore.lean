import Foundation.FourCubeBoundarySmoothPartition
import Foundation.HilbertRepresentation
import Mathlib.MeasureTheory.Function.L2Space
/-! Native conditional score for the actual all32-link Haar Wilson cell.
The boundary family is the existing three-axis family and the integration
space is fixed. The bounded score functional is constructed in its native L2,
not in a covariance-induced replacement norm. No uniform multiblock bound
or closed spatial gradient is asserted. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourCubeConditionalScore
open FourCubeHaarContinuousIntegral FourCubeBoundarySmoothAction
open FourCubeHaarParity FourCubeIntegratedCubic
attribute [local irreducible] action haarIntegral

def weight (β : ℝ) (a : Parameters) : Observables := NormedSpace.exp ((-β) • action a)

def expectation (β : ℝ) (a : Parameters) (f : Observables) : ℝ :=
  haarIntegral (f*weight β a)/FourCubeBoundarySmoothPartition.partition β a

def actionDirection (a u : Parameters) : Observables := fderiv ℝ action a u

def response (β : ℝ) (a u : Parameters) (f : Observables) : ℝ :=
  -β*(expectation β a (f*actionDirection a u)-expectation β a f*expectation β a (actionDirection a u))

theorem partition_pos (β : ℝ) (a : Parameters) :
    0 < FourCubeBoundarySmoothPartition.partition β a := by
  rw [FourCubeBoundarySmoothPartition.partition_eq_actual]
  exact FourCubeIntegratedResponse.partition3_pos _ _ _ _

theorem weight_apply (β : ℝ) (a : Parameters) (s : InteriorState) :
    weight β a s=Real.exp (-β*cellAction (a 0) (a 1) (a 2) s) := by
  rw [weight,exp_apply]
  simp only [ContinuousMap.smul_apply,smul_eq_mul,action_apply]

theorem weight_hasDerivAt (β : ℝ) (a u : Parameters) :
    HasDerivAt (fun t : ℝ => weight β (a+t • u))
      (weight β a*((-β) • actionDirection a u)) 0 := by
  have hline : HasDerivAt (fun t : ℝ => a+t • u) u 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const u |>.const_add a
  have hA := ((action_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt).comp_hasDerivAt 0 hline
  have hE := (hasFDerivAt_exp (𝕂 := ℝ)).comp_hasDerivAt 0 (hA.const_smul (-β))
  simpa only [Function.comp_def,Pi.smul_apply,zero_smul,add_zero,ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,
    smul_eq_mul,weight,actionDirection] using hE

theorem weighted_hasDerivAt (β : ℝ) (a u : Parameters) (f : Observables) :
    HasDerivAt (fun t : ℝ => haarIntegral (f*weight β (a+t • u)))
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

theorem expectation_hasDerivAt (β : ℝ) (a u : Parameters) (f : Observables) :
    HasDerivAt (fun t : ℝ => expectation β (a+t • u) f) (response β a u f) 0 := by
  have h1 := weighted_hasDerivAt β a u f
  have h0 := weighted_hasDerivAt β a u 1
  simp only [one_mul] at h0
  have hz : haarIntegral (weight β (a+(0:ℝ) • u))≠0 := by
    change FourCubeBoundarySmoothPartition.partition β (a+(0:ℝ) • u)≠0
    simpa only [zero_smul,add_zero] using (partition_pos β a).ne'
  have h := h1.div h0 hz
  convert h using 1
  · rfl
  · unfold response expectation FourCubeBoundarySmoothPartition.partition
    simp only [zero_smul,add_zero]
    have hz0 : haarIntegral (NormedSpace.exp ((-β) • action a))≠0 := (partition_pos β a).ne'
    dsimp only [weight]
    field_simp [hz0]
    <;> ring

/-- Actual normalized product-Haar Gibbs law, with every32 interior link integrated. -/
def source (a : Parameters) (s : InteriorState) : ℝ := -action a s/144

theorem source_measurable (a : Parameters) : Measurable (source a) :=
  (action a).continuous.measurable.neg.div_const _

theorem source_bound (a : Parameters) (s : InteriorState) : |source a s|≤1 := by
  have h := cellAction_bounds (a 0) (a 1) (a 2) s
  rw [source,action_apply,abs_div,abs_neg,abs_of_nonneg h.1]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<144)]
  exact (div_le_one (by norm_num : (0:ℝ)<144)).mpr h.2

def law (β : ℝ) (a : Parameters) : Measure InteriorState :=
  BoundedExponentialTiltResponse.tiltedMeasure interiorHaar (source a) (144*β)

instance law_probability (β : ℝ) (a : Parameters) : IsProbabilityMeasure (law β a) :=
  BoundedExponentialTiltResponse.tiltedMeasure_probability interiorHaar (source a)
    (source_measurable a) (source_bound a) (144*β)

theorem law_integral (β : ℝ) (a : Parameters) (f : Observables) :
    (∫ s,f s ∂law β a)=expectation β a f := by
  rw [law,BoundedExponentialTiltResponse.tilted_integral interiorHaar (source a) f
    (source_measurable a) (source_bound a)]
  have he (s : InteriorState) : (144*β)*source a s = -β*action a s := by unfold source; ring
  unfold BoundedExponentialTiltResponse.expectation BoundedExponentialTiltResponse.weighted
    BoundedExponentialTiltResponse.partition expectation
  simp_rw [he]
  rw [haarIntegral_apply]
  congr 1
  · apply integral_congr_ae
    filter_upwards with s
    simp only [ContinuousMap.mul_apply,weight,exp_apply,ContinuousMap.smul_apply,smul_eq_mul]
  · unfold FourCubeBoundarySmoothPartition.partition
    rw [haarIntegral_apply]
    apply integral_congr_ae
    filter_upwards with s
    simp only [exp_apply,ContinuousMap.smul_apply,smul_eq_mul]
    rw [he]
    simp

def score (β : ℝ) (a u : Parameters) : Observables :=
  (-β) • (actionDirection a u-ContinuousMap.const _ (expectation β a (actionDirection a u)))

abbrev Native (β : ℝ) (a : Parameters) := Lp ℝ 2 (law β a)

def nativeScore (β : ℝ) (a u : Parameters) : Native β a :=
  ContinuousMap.toLp 2 (law β a) ℝ (score β a u)

/-- Bounded adjoint-type response on the ORIGINAL native L2. -/
def nativeResponse (β : ℝ) (a u : Parameters) : Native β a →L[ℝ] ℝ :=
  innerSL ℝ (nativeScore β a u)

theorem observable_integrable_native (β : ℝ) (a : Parameters) (f : Observables) :
    Integrable f (law β a) :=
  Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (fun s => f.norm_coe_le_norm s))

theorem nativeResponse_core (β : ℝ) (a u : Parameters) (f : Observables) :
    nativeResponse β a u (ContinuousMap.toLp 2 (law β a) ℝ f)=response β a u f := by
  rw [nativeResponse,innerSL_apply_apply,nativeScore,ContinuousMap.inner_toLp]
  have he : (fun s => f s * starRingEnd ℝ (score β a u s))=
      (fun s => -β*((f*actionDirection a u) s-f s*expectation β a (actionDirection a u))) := by
    funext s
    simp only [starRingEnd_apply,star_trivial,score,ContinuousMap.smul_apply,
      ContinuousMap.sub_apply,ContinuousMap.const_apply,ContinuousMap.mul_apply,smul_eq_mul]
    ring
  rw [he,integral_const_mul,
    integral_sub (observable_integrable_native β a (f*actionDirection a u))
      ((observable_integrable_native β a f).mul_const _),integral_mul_const,
    law_integral,law_integral]
  rfl

/-- Differentiation is actual along any stated boundary direction on the continuous core. -/
theorem native_derivative (β : ℝ) (a u : Parameters) (f : Observables) :
    HasDerivAt (fun t : ℝ => ∫ s,f s ∂law β (a+t • u))
      (nativeResponse β a u (ContinuousMap.toLp 2 (law β a) ℝ f)) 0 := by
  simp_rw [law_integral,nativeResponse_core]
  exact expectation_hasDerivAt β a u f

theorem nativeResponse_norm (β : ℝ) (a u : Parameters) :
    ‖nativeResponse β a u‖=‖nativeScore β a u‖ := innerSL_apply_norm ℝ (nativeScore β a u)

theorem nativeResponse_self (β : ℝ) (a u : Parameters) :
    nativeResponse β a u (nativeScore β a u)=‖nativeScore β a u‖^2 := by
  rw [nativeResponse,innerSL_apply_apply,real_inner_self_eq_norm_sq]

/-- This tests the response bound in the original native L2 norm, with the sharp constant. -/
theorem native_bound_iff (β : ℝ) (a u : Parameters) (C : ℝ) (hC : 0≤C) :
    (∀ v : Native β a, |nativeResponse β a u v|≤C*‖v‖) ↔ ‖nativeScore β a u‖≤C := by
  rw [← nativeResponse_norm]
  constructor
  · intro h
    exact (nativeResponse β a u).opNorm_le_bound hC (fun v => by simpa only [Real.norm_eq_abs] using h v)
  · intro h v
    rw [← Real.norm_eq_abs]
    exact ((nativeResponse β a u).le_opNorm v).trans (mul_le_mul_of_nonneg_right h (norm_nonneg v))

/-- Exact Fisher/score energy; finiteness is native L2 membership, not a formal symbol. -/
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

theorem expectation_one (β : ℝ) (a : Parameters) : expectation β a 1=1 := by
  rw [← law_integral]
  simp

theorem nativeResponse_one (β : ℝ) (a u : Parameters) :
    nativeResponse β a u (ContinuousMap.toLp 2 (law β a) ℝ 1)=0 := by
  rw [nativeResponse_core,response,one_mul,expectation_one,one_mul,sub_self,mul_zero]

/-- Uniform estimates for this actual response are exactly native score variance estimates.
No covariance-completion norm can replace the norm on the left-hand side. -/
theorem native_bound_variance_iff (β : ℝ) (a u : Parameters) (C : ℝ) (hC : 0≤C) :
    (∀ v : Native β a, |nativeResponse β a u v|≤C*‖v‖) ↔
      β^2*ProbabilityTheory.variance (actionDirection a u) (law β a)≤C^2 := by
  rw [native_bound_iff β a u C hC,← nativeScore_norm_square]
  constructor
  · intro h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  · intro h
    nlinarith [norm_nonneg (nativeScore β a u)]

/-- The direct derivative of a varying observable is retained alongside the score channel. -/
theorem moving_expectation_hasDerivAt (β : ℝ) (a u : Parameters)
    (F : ℝ → Observables) (dF : Observables) (hF : HasDerivAt F dF 0) :
    HasDerivAt (fun t : ℝ => expectation β (a+t • u) (F t))
      (expectation β a dF+response β a u (F 0)) 0 := by
  have hw := haarIntegral.hasFDerivAt.comp_hasDerivAt 0 (hF.mul (weight_hasDerivAt β a u))
  have h0 := weighted_hasDerivAt β a u 1
  simp only [one_mul] at h0
  have hz : haarIntegral (weight β (a+(0:ℝ) • u))≠0 := by
    change FourCubeBoundarySmoothPartition.partition β (a+(0:ℝ) • u)≠0
    simpa only [zero_smul,add_zero] using (partition_pos β a).ne'
  have h := hw.div h0 hz
  convert h using 1
  · rfl
  · simp only [Function.comp_def,Pi.mul_apply,zero_smul,add_zero]
    rw [show F 0*(weight β a*((-β) • actionDirection a u))=
      (-β) • ((F 0*actionDirection a u)*weight β a) by
        ext s
        simp only [ContinuousMap.mul_apply,ContinuousMap.smul_apply,smul_eq_mul]
        ring,map_add,map_smul]
    unfold response expectation FourCubeBoundarySmoothPartition.partition weight
    have hz0 : haarIntegral (NormedSpace.exp ((-β) • action a))≠0 := (partition_pos β a).ne'
    field_simp [hz0]
    ring

def potential (β : ℝ) (a : Parameters) : ℝ :=
  -Real.log (FourCubeBoundarySmoothPartition.partition β a)

theorem potential_hasDerivAt (β : ℝ) (a u : Parameters) :
    HasDerivAt (fun t : ℝ => potential β (a+t • u))
      (β*expectation β a (actionDirection a u)) 0 := by
  have h0 := weighted_hasDerivAt β a u 1
  simp only [one_mul] at h0
  have hz : haarIntegral (weight β (a+(0:ℝ) • u))≠0 := by
    change FourCubeBoundarySmoothPartition.partition β (a+(0:ℝ) • u)≠0
    simpa only [zero_smul,add_zero] using (partition_pos β a).ne'
  convert (h0.log hz).neg using 1
  · rfl
  · simp only [zero_smul,add_zero]
    unfold expectation FourCubeBoundarySmoothPartition.partition weight
    ring

def actionSecond (a u v : Parameters) : Observables :=
  fderiv ℝ (fun b => actionDirection b u) a v

/-- The actual integrated mixed Hessian retains both direct geometry and the native score channel. -/
theorem potential_mixed_response (β : ℝ) (a u v : Parameters) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => potential β (a+t • v+s • u)) 0) 0 =
      β*(expectation β a (actionSecond a u v)+
        nativeResponse β a v (ContinuousMap.toLp 2 (law β a) ℝ (actionDirection a u))) := by
  have hD : ContDiff ℝ ∞ (fun b => actionDirection b u) :=
    (action_contDiff.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hline : HasDerivAt (fun t : ℝ => a+t • v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const v |>.const_add a
  have hd := (hD.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hline
  have hd0 : HasDerivAt (fun t : ℝ => actionDirection (a+t • v) u) (actionSecond a u v) 0 := by
    simpa only [Function.comp_def,zero_smul,add_zero,actionSecond] using hd
  have hm := (moving_expectation_hasDerivAt β a v _ _ hd0).const_mul β
  have he : (fun t : ℝ => deriv (fun s : ℝ => potential β (a+t • v+s • u)) 0)=
      (fun t => β*expectation β (a+t • v) (actionDirection (a+t • v) u)) := by
    funext t
    exact (potential_hasDerivAt β (a+t • v) u).deriv
  rw [he,nativeResponse_core]
  simpa only [zero_smul,add_zero] using hm.deriv

/-- No quadratic/Gaussian substitution has removed the nonlinear mean second variation. -/
theorem potential_mixed_covariance (β : ℝ) (a u v : Parameters) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => potential β (a+t • v+s • u)) 0) 0 =
      β*expectation β a (actionSecond a u v)-β^2*
        (expectation β a (actionDirection a u*actionDirection a v)-
          expectation β a (actionDirection a u)*expectation β a (actionDirection a v)) := by
  rw [potential_mixed_response,nativeResponse_core]
  unfold response
  ring

/-- Normalizing by the reference partition changes only a boundary-independent scalar. -/
theorem potential_eq_actual (β : ℝ) (a : Parameters) :
    potential β a=FourCubeBoundarySmoothPartition.freeEnergy β a-
      Real.log (FourCubePinnedConcentration.normalizer β) := by
  unfold potential FourCubeBoundarySmoothPartition.freeEnergy
    FourCubeThermalMixedDifference.freeEnergy FourCubeScaledBoundaryControl.normalizedPartition
  rw [FourCubeBoundarySmoothPartition.partition_eq_actual,FourCubePinnedHaar.partition3_eq_pinned,
    Real.log_div (FourCubePinnedHaar.pinnedPartition_positive _ _).ne'
      (FourCubePinnedConcentration.normalizer_positive _).ne']
  ring

/-- The same exact decomposition for the EXISTING actual normalized free energy. -/
theorem actual_mixed_response (β : ℝ) (a u v : Parameters) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      FourCubeBoundarySmoothPartition.freeEnergy β (a+t • v+s • u)) 0) 0 =
      β*(expectation β a (actionSecond a u v)+
        nativeResponse β a v (ContinuousMap.toLp 2 (law β a) ℝ (actionDirection a u))) := by
  have h := potential_mixed_response β a u v
  simp_rw [potential_eq_actual,deriv_sub_const] at h
  exact h

theorem score_self_response (β : ℝ) (a u : Parameters) :
    ‖nativeScore β a u‖^2=
      -β*nativeResponse β a u (ContinuousMap.toLp 2 (law β a) ℝ (actionDirection a u)) := by
  have hc : ContinuousMap.const InteriorState (expectation β a (actionDirection a u))=
      expectation β a (actionDirection a u) • (1:Observables) := by
    ext s
    simp only [ContinuousMap.const_apply,ContinuousMap.smul_apply,ContinuousMap.one_apply,
      smul_eq_mul,mul_one]
  have hn : nativeScore β a u=(-β) •
      (ContinuousMap.toLp 2 (law β a) ℝ (actionDirection a u)-
        expectation β a (actionDirection a u) • ContinuousMap.toLp 2 (law β a) ℝ 1) := by
    rw [nativeScore,score,hc,map_smul,map_sub,map_smul]
  have h := congrArg (nativeResponse β a u) hn
  rw [nativeResponse_self,map_smul,map_sub,map_smul,nativeResponse_one,smul_zero,sub_zero] at h
  exact h

/-- The integrated diagonal Hessian has the negative, exact native score-energy correction. -/
theorem actual_diagonal_hessian (β : ℝ) (a u : Parameters) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      FourCubeBoundarySmoothPartition.freeEnergy β (a+t • u+s • u)) 0) 0 =
      β*expectation β a (actionSecond a u u)-‖nativeScore β a u‖^2 := by
  rw [actual_mixed_response,score_self_response]
  ring
end OperatorDerivativeRewrite.Foundation.FourCubeConditionalScore
