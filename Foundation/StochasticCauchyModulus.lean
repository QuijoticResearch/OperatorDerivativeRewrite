import Foundation.StochasticCauchyContinuousPolynomials
import Foundation.GaussianQuadraticIto

/-! Actual nonanalytic Brownian modulus-square reconstruction in both native
complex channels. No holomorphic reconstruction theorem is used for barZ. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyModulus
open InfiniteGaussian ProductL2Curry ComplexL2Isometry GaussianTimeProcess
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyPolynomialInput
open StochasticCauchyPolynomialPrediction StochasticCauchyPolynomialSums
open GaussianBrownianQuadraticVariation GaussianQuadraticRepresentation
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyComplexChannels.complexInput_complete

private def pick (b : Bool) (w : SampleSpace × SampleSpace) : SampleSpace := if b then w.2 else w.1
private theorem pick_preserving (b : Bool) : MeasurePreserving (pick b)
    (gaussianProduct.prod gaussianProduct) gaussianProduct := by
  cases b
  · exact measurePreserving_fst
  · exact measurePreserving_snd
private def liftSource (b : Bool) : GaussianL2 →ₗᵢ[ℝ] JointL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (pick b) (pick_preserving b)
private theorem liftSource_ae (b : Bool) (f : GaussianL2) :
    liftSource b f =ᵐ[gaussianProduct.prod gaussianProduct] fun w => f (pick b w) :=
  Lp.coeFn_compMeasurePreserving f (pick_preserving b)
private def noiseIntegral (T : ℝ≥0) (b : Bool) : Input T →ₗᵢ[ℝ] JointL2 :=
  if b then integralY T else integralX T

private theorem diagonal_step (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (b : Bool) :
    noiseIntegral T b (polynomialStep T s t hst htT Polynomial.X b)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        process s (pick b w)*(process t (pick b w)-process s (pick b w)) := by
  cases b
  · simpa [noiseIntegral,pick,valuePartValue,position] using
      (polynomial_step_ae T s t hst htT Polynomial.X false).1
  · simpa [noiseIntegral,pick,valuePartValue,position] using
      (polynomial_step_ae T s t hst htT Polynomial.X true).2

/-- Exact finite identification with the previously verified scalar stochastic sums. -/
theorem diagonal_grid (T : ℝ≥0) (N : ℕ) (b : Bool) :
    noiseIntegral T b (gridInput T Polynomial.X b N)=
      liftSource b (GaussianPredictableFull.itoIntegral (leftStepField (uniformTime T N))) := by
  rw [gridInput,map_sum]
  apply Lp.ext
  have he (i : Fin (N+1)) := diagonal_step T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    (by simpa only [(uniformTime_endpoints T N).2] using uniformTime_monotone T N (Fin.le_last i.succ)) b
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N+1) => noiseIntegral T b
      (polynomialStep T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))
        (by simpa only [(uniformTime_endpoints T N).2] using uniformTime_monotone T N (Fin.le_last i.succ)) Polynomial.X b)),
    ae_all_iff.mpr he,liftSource_ae b (GaussianPredictableFull.itoIntegral (leftStepField (uniformTime T N))),
    (pick_preserving b).quasiMeasurePreserving.ae_eq_comp
      (integral_leftStepField_coeFn (uniformTime T N) (uniformTime_monotone T N))] with w hs he hl hi
  rw [hs,hl]
  simp only [Finset.sum_apply,Function.comp_apply] at *
  rw [hi]
  exact Finset.sum_congr rfl (fun i _ => he i)

/-- Diagonal source integrals of the already constructed actual running inputs. -/
theorem diagonal_integral (T : ℝ≥0) (b : Bool) :
    noiseIntegral T b (partInput T Polynomial.X b)=(1/2:ℝ) • liftSource b (terminalSquare T) := by
  have hn := ((noiseIntegral T b).continuous.tendsto (partInput T Polynomial.X b)).comp
    (partInput_tendsto T Polynomial.X b)
  have hs := ((liftSource b).continuous.tendsto ((1/2:ℝ) • terminalSquare T)).comp
    (leftStep_integral_tendsto T)
  simp only [Function.comp_def,← diagonal_grid,map_smul] at hs
  exact tendsto_nhds_unique hn hs

private theorem normalized_anti_combine (T : ℝ≥0) (a b : Input T) :
    channel T true (((Real.sqrt 2:ℝ):ℂ) • combineInput T a b)=
      combine (gaussianProduct.prod gaussianProduct)
        (integralX T a+integralY T b) (integralX T b-integralY T a) := by
  have hs : (((Real.sqrt 2:ℝ):ℂ)*(((Real.sqrt 2)⁻¹:ℝ):ℂ))=1 := by
    rw [← Complex.ofReal_mul,mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))),Complex.ofReal_one]
  rw [map_smul]
  change ((Real.sqrt 2:ℝ):ℂ) • ((((Real.sqrt 2)⁻¹:ℝ):ℂ) •
    (liftInput T (integralX T) (combineInput T a b)+
      (-Complex.I) • liftInput T (integralY T) (combineInput T a b)))=_
  rw [smul_smul,hs,one_smul,liftInput_combine,liftInput_combine]
  simp only [combine,map_sub,map_add,smul_add,smul_sub,smul_smul,
    Complex.I_mul_I,neg_one_smul,neg_smul]
  simp only [neg_one_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul]
  abel

/-- false integrates barZ against dZ; true integrates Z against dbarZ.
The explicit sqrt2 cancels the original native channel normalization. -/
def modulusInput (T : ℝ≥0) (anti : Bool) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (partInput T Polynomial.X false)
    (if anti then partInput T Polynomial.X true else -partInput T Polynomial.X true)

def modulusOutput (T : ℝ≥0) (anti : Bool) : JointComplex := channel T anti (modulusInput T anti)

def modulusTarget (T : ℝ≥0) : JointComplex :=
  ofReal (gaussianProduct.prod gaussianProduct) (liftSource false (terminalSquare T)+liftSource true (terminalSquare T))

theorem two_channel_identity (T : ℝ≥0) :
    modulusOutput T false+modulusOutput T true=modulusTarget T := by
  simp only [modulusOutput,modulusInput,Bool.false_eq_true,ite_false,ite_true,
    StochasticCauchyExponentialReconstruction.normalized_channel_combine,normalized_anti_combine,map_neg]
  simp only [combine,map_add,map_sub,map_neg,smul_add,smul_sub,smul_neg]
  have hx := diagonal_integral T false
  have hy := diagonal_integral T true
  simp only [noiseIntegral,Bool.false_eq_true,ite_false,ite_true] at hx hy
  rw [hx,hy]
  simp only [modulusTarget,map_add,map_smul]
  module

theorem modulus_target_actual (T : ℝ≥0) : modulusTarget T =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => ((‖position T w‖^2-2*(T:ℝ):ℝ):ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL (liftSource false (terminalSquare T)+liftSource true (terminalSquare T)),
    Lp.coeFn_add (liftSource false (terminalSquare T)) (liftSource true (terminalSquare T)),
    liftSource_ae false (terminalSquare T),liftSource_ae true (terminalSquare T),
    (pick_preserving false).quasiMeasurePreserving.ae_eq_comp (terminalSquare_coeFn T),
    (pick_preserving true).quasiMeasurePreserving.ae_eq_comp (terminalSquare_coeFn T)] with w ho ha hx hy hxt hyt
  change modulusTarget T w=_
  change modulusTarget T w= _ at ho
  simp only [Function.comp_apply,pick,Bool.false_eq_true,ite_false,ite_true] at hx hy hxt hyt
  rw [ho,ha]
  simp only [Pi.add_apply]
  rw [hx,hy,hxt,hyt]
  have hn : ‖position T w‖^2=(process T w.1)^2+(process T w.2)^2 := by
    simp [position,Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [hn]
  change ((((process T w.1)^2-(T:ℝ))+((process T w.2)^2-(T:ℝ)):ℝ):ℂ)=_
  congr 1
  ring

private theorem component_step (T s t : ℝ≥0) (hst : s≤t) (htT : t≤T) (b j : Bool) :
    noiseIntegral T j (polynomialStep T s t hst htT Polynomial.X b)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        process s (pick b w)*(process t (pick j w)-process s (pick j w)) := by
  cases j <;> cases b
  · simpa [noiseIntegral,pick,valuePartValue,position] using
      (polynomial_step_ae T s t hst htT Polynomial.X false).1
  · simpa [noiseIntegral,pick,valuePartValue,position] using
      (polynomial_step_ae T s t hst htT Polynomial.X true).1
  · simpa [noiseIntegral,pick,valuePartValue,position] using
      (polynomial_step_ae T s t hst htT Polynomial.X false).2
  · simpa [noiseIntegral,pick,valuePartValue,position] using
      (polynomial_step_ae T s t hst htT Polynomial.X true).2

private theorem component_grid (T : ℝ≥0) (N : ℕ) (b j : Bool) :
    noiseIntegral T j (gridInput T Polynomial.X b N) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => ∑ i : Fin (N+1),process (uniformTime T N i.castSucc) (pick b w)*
        (process (uniformTime T N i.succ) (pick j w)-process (uniformTime T N i.castSucc) (pick j w)) := by
  rw [gridInput,map_sum]
  have he (i : Fin (N+1)) := component_step T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
    (uniformTime_monotone T N (Fin.castSucc_le_succ i))
    (by simpa only [(uniformTime_endpoints T N).2] using uniformTime_monotone T N (Fin.le_last i.succ)) b j
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i : Fin (N+1) => noiseIntegral T j
      (polynomialStep T (uniformTime T N i.castSucc) (uniformTime T N i.succ)
        (uniformTime_monotone T N (Fin.castSucc_le_succ i))
        (by simpa only [(uniformTime_endpoints T N).2] using uniformTime_monotone T N (Fin.le_last i.succ)) Polynomial.X b)),
    ae_all_iff.mpr he] with w hs he
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => he i)

private theorem modulus_combine (T : ℝ≥0) (anti : Bool) (a b : Input T) :
    channel T anti (((Real.sqrt 2:ℝ):ℂ) • combineInput T a (if anti then b else -b))=
      combine (gaussianProduct.prod gaussianProduct) (integralX T a+integralY T b)
        (if anti then integralX T b-integralY T a else -(integralX T b-integralY T a)) := by
  cases anti
  · simp only [Bool.false_eq_true,ite_false,StochasticCauchyExponentialReconstruction.normalized_channel_combine,map_neg,sub_neg_eq_add]
    congr 1
    abel
  · simp only [ite_true,normalized_anti_combine]

def modulusSteps (T : ℝ≥0) (anti : Bool) (N : ℕ) : ComplexInput T :=
  ((Real.sqrt 2:ℝ):ℂ) • combineInput T (gridInput T Polynomial.X false N)
    (if anti then gridInput T Polynomial.X true N else -gridInput T Polynomial.X true N)

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

theorem modulus_steps_tendsto (T : ℝ≥0) (anti : Bool) :
    Tendsto (modulusSteps T anti) atTop (𝓝 (modulusInput T anti)) := by
  cases anti
  · exact tendsto_const_nhds.smul (combineInput_tendsto T _ _ _ _
      (partInput_tendsto T Polynomial.X false) (partInput_tendsto T Polynomial.X true).neg)
  · exact tendsto_const_nhds.smul (combineInput_tendsto T _ _ _ _
      (partInput_tendsto T Polynomial.X false) (partInput_tendsto T Polynomial.X true))

theorem modulus_outputs_tendsto (T : ℝ≥0) (anti : Bool) :
    Tendsto (fun N => channel T anti (modulusSteps T anti N)) atTop (𝓝 (modulusOutput T anti)) :=
  ((channel T anti).continuous.tendsto _).comp (modulus_steps_tendsto T anti)

/-- Actual conjugated products; false is barZ*dZ, true is Z*dbarZ. -/
def physicalSum (T : ℝ≥0) (anti : Bool) (N : ℕ) (w : SampleSpace × SampleSpace) : ℂ :=
  ∑ i : Fin (N+1),
    (if anti then position (uniformTime T N i.castSucc) w else star (position (uniformTime T N i.castSucc) w))*
    (if anti then star (position (uniformTime T N i.succ) w-position (uniformTime T N i.castSucc) w)
      else position (uniformTime T N i.succ) w-position (uniformTime T N i.castSucc) w)

theorem modulus_steps_actual (T : ℝ≥0) (anti : Bool) (N : ℕ) :
    channel T anti (modulusSteps T anti N) =ᵐ[gaussianProduct.prod gaussianProduct] physicalSum T anti N := by
  rw [modulusSteps,modulus_combine]
  let a := integralX T (gridInput T Polynomial.X false N)
  let b := integralY T (gridInput T Polynomial.X true N)
  let c := integralX T (gridInput T Polynomial.X true N)
  let d := integralY T (gridInput T Polynomial.X false N)
  filter_upwards [combine_ae (gaussianProduct.prod gaussianProduct) (a+b) (if anti then c-d else -(c-d)),
    Lp.coeFn_add a b,Lp.coeFn_sub c d,Lp.coeFn_neg (c-d),
    component_grid T N false false,component_grid T N true true,
    component_grid T N true false,component_grid T N false true] with w hc ha hd hn hxx hyy hyx hxy
  change a w=_ at hxx
  change b w=_ at hyy
  change c w=_ at hyx
  change d w=_ at hxy
  cases anti <;> simp only [Bool.false_eq_true,ite_false,ite_true] at *
  · rw [hc,ha,hn,Pi.neg_apply,hd]
    simp only [Pi.add_apply,Pi.sub_apply,hxx,hyy,hyx,hxy]
    apply Complex.ext <;>
      simp [physicalSum,position,pick,Complex.mul_re,Complex.mul_im] <;>
      simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_neg_distrib] <;>
      apply Finset.sum_congr rfl <;> intro i _ <;> ring
  · rw [hc,ha,hd]
    simp only [Pi.add_apply,Pi.sub_apply,hxx,hyy,hyx,hxy]
    apply Complex.ext <;>
      simp [physicalSum,position,pick,Complex.mul_re,Complex.mul_im] <;>
      simp only [← Finset.sum_add_distrib,← Finset.sum_sub_distrib,← Finset.sum_neg_distrib] <;>
      apply Finset.sum_congr rfl <;> intro i _ <;> ring

theorem physical_sum_memLp (T : ℝ≥0) (anti : Bool) (N : ℕ) :
    MemLp (physicalSum T anti N) 2 (gaussianProduct.prod gaussianProduct) :=
  (Lp.memLp (channel T anti (modulusSteps T anti N))).ae_eq (modulus_steps_actual T anti N)

theorem physical_sum_mean_square (T : ℝ≥0) (anti : Bool) :
    Tendsto (fun N => ∫ w,‖physicalSum T anti N w-modulusOutput T anti w‖^2
      ∂gaussianProduct.prod gaussianProduct) atTop (𝓝 0) := by
  have he (N : ℕ) : ‖channel T anti (modulusSteps T anti N)-modulusOutput T anti‖^2=
      ∫ w,‖physicalSum T anti N w-modulusOutput T anti w‖^2 ∂gaussianProduct.prod gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (channel T anti (modulusSteps T anti N)) (modulusOutput T anti),
      modulus_steps_actual T anti N] with w hd hs
    simp only [Pi.sub_apply] at hd
    rw [hd,hs]
  have ht := ((modulus_outputs_tendsto T anti).sub
    (tendsto_const_nhds (x := modulusOutput T anti))).norm.pow 2
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht

theorem canonical_inputs (T : ℝ≥0) :
    channelAdjoint T false (modulusTarget T)=modulusInput T false ∧
    channelAdjoint T true (modulusTarget T)=modulusInput T true := by
  rw [← two_channel_identity]
  exact channel_coefficients_recover T _ _

theorem modulus_residual_zero (T : ℝ≥0) : residual T (modulusTarget T)=0 := by
  rw [reconstruction_iff]
  exact ⟨modulusInput T false,modulusInput T true,(two_channel_identity T).symm⟩

/-- Actual continuous-path sums. Only fixed-time AE modification bridges are used. -/
def continuousSum (T : ℝ≥0) (anti : Bool) (N : ℕ) (w : SampleSpace × SampleSpace) : ℂ :=
  ∑ i : Fin (N+1),
    (if anti then StochasticCauchyBrownianRealization.value (uniformTime T N i.castSucc) w
      else star (StochasticCauchyBrownianRealization.value (uniformTime T N i.castSucc) w))*
    (if anti then star (StochasticCauchyBrownianRealization.value (uniformTime T N i.succ) w-
        StochasticCauchyBrownianRealization.value (uniformTime T N i.castSucc) w)
      else StochasticCauchyBrownianRealization.value (uniformTime T N i.succ) w-
        StochasticCauchyBrownianRealization.value (uniformTime T N i.castSucc) w)

theorem continuous_sum_ae (T : ℝ≥0) (anti : Bool) (N : ℕ) :
    continuousSum T anti N =ᵐ[gaussianProduct.prod gaussianProduct] physicalSum T anti N := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin (N+1) =>
      StochasticCauchyContinuousPolynomials.continuous_value_ae (uniformTime T N i.castSucc)),
    ae_all_iff.mpr (fun i : Fin (N+1) =>
      StochasticCauchyContinuousPolynomials.continuous_value_ae (uniformTime T N i.succ))] with w hl hr
  unfold continuousSum physicalSum
  exact Finset.sum_congr rfl (fun i _ => by rw [hl i,hr i])

theorem continuous_chronological (T : ℝ≥0) (anti : Bool) (N : ℕ) :
    channel T anti (modulusSteps T anti N) =ᵐ[gaussianProduct.prod gaussianProduct] continuousSum T anti N :=
  (modulus_steps_actual T anti N).trans (continuous_sum_ae T anti N).symm

theorem continuous_sum_memLp (T : ℝ≥0) (anti : Bool) (N : ℕ) :
    MemLp (continuousSum T anti N) 2 (gaussianProduct.prod gaussianProduct) :=
  (physical_sum_memLp T anti N).ae_eq (continuous_sum_ae T anti N).symm

theorem continuous_sum_mean_square (T : ℝ≥0) (anti : Bool) :
    Tendsto (fun N => ∫ w,‖continuousSum T anti N w-modulusOutput T anti w‖^2
      ∂gaussianProduct.prod gaussianProduct) atTop (𝓝 0) := by
  have he (N : ℕ) : (∫ w,‖continuousSum T anti N w-modulusOutput T anti w‖^2
      ∂gaussianProduct.prod gaussianProduct)=
      ∫ w,‖physicalSum T anti N w-modulusOutput T anti w‖^2 ∂gaussianProduct.prod gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [continuous_sum_ae T anti N] with w hw
    rw [hw]
  simpa only [he] using physical_sum_mean_square T anti

theorem continuous_target_actual (T : ℝ≥0) : modulusTarget T =ᵐ[gaussianProduct.prod gaussianProduct]
    fun w => ((‖StochasticCauchyBrownianRealization.value T w‖^2-2*(T:ℝ):ℝ):ℂ) := by
  filter_upwards [modulus_target_actual T,StochasticCauchyContinuousPolynomials.continuous_value_ae T] with w ht hz
  rw [ht,hz]

/-- The actual two native stochastic integrals reconstruct the nonanalytic
centered modulus of the already constructed continuous Brownian process. -/
theorem continuous_two_channel (T : ℝ≥0) :
    (fun w => modulusOutput T false w+modulusOutput T true w) =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => ((‖StochasticCauchyBrownianRealization.value T w‖^2-2*(T:ℝ):ℝ):ℂ) := by
  have he := continuous_target_actual T
  rw [← two_channel_identity] at he
  filter_upwards [he,Lp.coeFn_add (modulusOutput T false) (modulusOutput T true)] with w he ha
  simp only [Pi.add_apply] at ha
  rw [← ha,he]

theorem modulus_input_parts (T : ℝ≥0) (anti : Bool) :
    realInput T (modulusInput T anti)=Real.sqrt 2 • partInput T Polynomial.X false ∧
    imagInput T (modulusInput T anti)=Real.sqrt 2 •
      (if anti then partInput T Polynomial.X true else -partInput T Polynomial.X true) := by
  constructor <;>
    simp only [modulusInput,realInput_smul,imagInput_smul,realInput_combine,imagInput_combine,
      Complex.ofReal_re,Complex.ofReal_im,zero_smul,sub_zero,add_zero]

/-- The combined actual continuous-path stochastic sums reconstruct the
correctly centered NONANALYTIC observable in physical mean square. -/
theorem continuous_reconstruction_mean_square (T : ℝ≥0) :
    Tendsto (fun N => ∫ w,‖continuousSum T false N w+continuousSum T true N w-
      (((‖StochasticCauchyBrownianRealization.value T w‖^2-2*(T:ℝ):ℝ):ℂ))‖^2
      ∂gaussianProduct.prod gaussianProduct) atTop (𝓝 0) := by
  let f := fun N => channel T false (modulusSteps T false N)+channel T true (modulusSteps T true N)
  have hf : Tendsto f atTop (𝓝 (modulusTarget T)) := by
    simpa only [two_channel_identity] using (modulus_outputs_tendsto T false).add (modulus_outputs_tendsto T true)
  have he (N : ℕ) : ‖f N-modulusTarget T‖^2=∫ w,‖continuousSum T false N w+continuousSum T true N w-
      (((‖StochasticCauchyBrownianRealization.value T w‖^2-2*(T:ℝ):ℝ):ℂ))‖^2 ∂gaussianProduct.prod gaussianProduct := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f N) (modulusTarget T),
      Lp.coeFn_add (channel T false (modulusSteps T false N)) (channel T true (modulusSteps T true N)),
      continuous_chronological T false N,continuous_chronological T true N,continuous_target_actual T]
      with w hd ha hfalse htrue ht
    simp only [Pi.add_apply,Pi.sub_apply] at hd ha
    change (f N) w=_ at ha
    rw [hd,ha,hfalse,htrue,ht]
  have ht := (hf.sub (tendsto_const_nhds (x := modulusTarget T))).norm.pow 2
  simpa only [he,sub_self,norm_zero,zero_pow (by decide : (2:ℕ)≠0)] using ht

end OperatorDerivativeRewrite.Foundation.StochasticCauchyModulus
