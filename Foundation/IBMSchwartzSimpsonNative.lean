import Foundation.IBMSchwartzHybridReconstruction
import Foundation.IBMSimpsonL2Error
import Foundation.IBMRawInitialPast

/-! Unclipped actual physical-time Simpson sums for shifted Schwartz primitives
converge in joint L2 to the explicit ORIGINAL intrinsic divergence plus its
necessary deterministic mean correction. No integral map is defined by output. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzSimpsonNative
open InfiniteGaussian IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMCorrectionStein
open IBMConstructedSources
attribute [local irreducible] jointDerivative IBMSchwartzHybridReconstruction.integrand
  IBMSchwartzHybridReconstruction.centered IBMIntrinsicOperators.sourceDerivative
  IBMIntrinsicOperators.clockDerivative

theorem shifted_smooth (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ContDiff ℝ n (shiftedJet g a 0) :=
  (g.smooth n).comp (contDiff_const.add contDiff_id)

theorem iterated_shifted (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    iteratedDeriv n (shiftedJet g a 0) = shiftedJet g a n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratedDeriv_succ,ih,shiftedJet_deriv]

def errors (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (n : ℕ) : JointL2 :=
  IBMSimpsonL2Error.errorClass (shiftedJet g a 0) (shifted_smooth g a 5)
    (SchwartzMap.seminorm ℝ 0 0 (jet g 5))
    (fun z => by rw [iterated_shifted]; exact shiftedJet_bound g a 5 z) T n

theorem errors_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    errors g a T n =ᵐ[IBMSourceLaws.jointMeasure]
      IBMActualSimpson.error (shiftedJet g a 0) T n :=
  IBMSimpsonL2Error.errorClass_actual_ae _ _ _ _ _ _

def physicalValue (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointL2 :=
  IBMSchwartzHybridReconstruction.terminal g a T - Lp.const 2 IBMSourceLaws.jointMeasure (g a)

theorem physicalValue_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    physicalValue g a T =ᵐ[IBMSourceLaws.jointMeasure] fun p => g (a+ibmValue T p)-g a := by
  filter_upwards [Lp.coeFn_sub (IBMSchwartzHybridReconstruction.terminal g a T)
    (Lp.const 2 IBMSourceLaws.jointMeasure (g a)),
    IBMSchwartzHybridReconstruction.terminal_actual g a T,
    Lp.coeFn_const 2 IBMSourceLaws.jointMeasure (g a)] with p hs ht hc
  change (IBMSchwartzHybridReconstruction.terminal g a T -
    Lp.const 2 IBMSourceLaws.jointMeasure (g a)) p = _
  rw [hs,Pi.sub_apply,ht,hc]
  rfl

def sumsClass (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (n : ℕ) : JointL2 :=
  errors g a T n + physicalValue g a T

theorem sumsClass_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    sumsClass g a T n =ᵐ[IBMSourceLaws.jointMeasure]
      IBMActualSimpson.sums (shiftedJet g a 1) T n := by
  filter_upwards [errors_actual g a T n,physicalValue_actual g a T,
    Lp.coeFn_add (errors g a T n) (physicalValue g a T),IBMRawInitialPast.ibm_zero_ae]
    with p he hv ha hz
  change (errors g a T n+physicalValue g a T) p = _
  rw [ha,Pi.add_apply,he,hv,IBMActualSimpson.error,shiftedJet_deriv]
  have h0 : shiftedJet g a 0 (ibmValue 0 p) = g a := by
    simp only [hz,shiftedJet,jet,add_zero]
  have hT : shiftedJet g a 0 (ibmValue T p) = g (a+ibmValue T p) := rfl
  rw [h0,hT]
  ring

theorem sums_memLp (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    MemLp (IBMActualSimpson.sums (shiftedJet g a 1) T n) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (sumsClass g a T n)).ae_eq (sumsClass_actual g a T n)

theorem sumsClass_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    Tendsto (sumsClass g a T) atTop (𝓝 (physicalValue g a T)) := by
  have h : Tendsto (errors g a T) atTop (𝓝 0) :=
    IBMSimpsonL2Error.errorClass_tendsto (shiftedJet g a 0) (shifted_smooth g a 5)
      (SchwartzMap.seminorm ℝ 0 0 (jet g 5))
      (fun z => by rw [iterated_shifted]; exact shiftedJet_bound g a 5 z) T
  change Tendsto (fun n => errors g a T n+physicalValue g a T) atTop (𝓝 _)
  simpa only [zero_add] using h.add (tendsto_const_nhds (x := physicalValue g a T))

def meanShift (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) : JointL2 :=
  IBMSchwartzHybridReconstruction.meanValue g a T - Lp.const 2 IBMSourceLaws.jointMeasure (g a)

theorem meanShift_actual (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    meanShift g a T =ᵐ[IBMSourceLaws.jointMeasure] fun _ =>
      (∫ p, g (a+ibmValue T p) ∂IBMSourceLaws.jointMeasure)-g a := by
  filter_upwards [Lp.coeFn_sub (IBMSchwartzHybridReconstruction.meanValue g a T)
    (Lp.const 2 IBMSourceLaws.jointMeasure (g a)),
    IBMSchwartzHybridReconstruction.meanValue_actual g a T,
    Lp.coeFn_const 2 IBMSourceLaws.jointMeasure (g a)] with p hs hm hc
  change (IBMSchwartzHybridReconstruction.meanValue g a T-
    Lp.const 2 IBMSourceLaws.jointMeasure (g a)) p = _
  rw [hs,Pi.sub_apply,hm,hc,IBMSchwartzHybridReconstruction.global_mean]
  rfl

theorem native_limit (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) :
    ∃ hi : IBMSchwartzHybridReconstruction.integrand g a T ∈ jointDivergence.domain,
      physicalValue g a T =
        (jointDivergence ⟨IBMSchwartzHybridReconstruction.integrand g a T,hi⟩ : JointL2) + meanShift g a T ∧
      Tendsto (sumsClass g a T) atTop
        (𝓝 ((jointDivergence ⟨IBMSchwartzHybridReconstruction.integrand g a T,hi⟩ : JointL2) +
          meanShift g a T)) := by
  obtain ⟨hi,hv⟩ := IBMSchwartzHybridReconstruction.reconstruction g a T
  have he : physicalValue g a T =
      (jointDivergence ⟨IBMSchwartzHybridReconstruction.integrand g a T,hi⟩ : JointL2)+meanShift g a T := by
    rw [hv]
    unfold IBMSchwartzHybridReconstruction.centered physicalValue meanShift
    change _ = (_-_)+(_-_)
    abel
  exact ⟨hi,he,he ▸ sumsClass_tendsto g a T⟩

theorem native_duality (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (F : jointDerivative.domain) :
    inner ℝ (physicalValue g a T-meanShift g a T) ((F : IntrinsicSpace) : JointL2) =
      inner ℝ (IBMSchwartzHybridReconstruction.integrand g a T) (jointDerivative F) := by
  have he : physicalValue g a T-meanShift g a T = (IBMSchwartzHybridReconstruction.centered g a T : JointL2) := by
    unfold physicalValue meanShift IBMSchwartzHybridReconstruction.centered
    change _-(_-_) = _-_
    abel
  rw [he]
  exact IBMSchwartzHybridReconstruction.terminal_duality g a T F

attribute [local irreducible] errors physicalValue sumsClass meanShift shiftedJet
  IBMActualSimpson.sums IBMConstructedSources.ibmValue

theorem actual_pairing_integrable (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (n : ℕ) (F : JointL2) :
    Integrable (fun p => IBMActualSimpson.sums (shiftedJet g a 1) T n p * F p)
      IBMSourceLaws.jointMeasure := (sums_memLp g a T n).integrable_mul (Lp.memLp F)

theorem pairing_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0) (f : JointL2) :
    Tendsto (fun n => ∫ p, IBMActualSimpson.sums (shiftedJet g a 1) T n p * f p
      ∂IBMSourceLaws.jointMeasure) atTop (𝓝 (inner ℝ f (physicalValue g a T))) := by
  have he (n : ℕ) : (∫ p, IBMActualSimpson.sums (shiftedJet g a 1) T n p * f p
      ∂IBMSourceLaws.jointMeasure) = inner ℝ f (sumsClass g a T n) := by
    rw [L2_inner_eq_integral]
    apply integral_congr_ae
    filter_upwards [sumsClass_actual g a T n] with p hp
    rw [hp,Real.inner_apply]
    ring
  have h := ((innerSL ℝ f).continuous.tendsto (physicalValue g a T)).comp
    (sumsClass_tendsto g a T)
  have hfun : (fun n => ∫ p, IBMActualSimpson.sums (shiftedJet g a 1) T n p * f p
      ∂IBMSourceLaws.jointMeasure) = fun n => inner ℝ f (sumsClass g a T n) := funext he
  change Tendsto (fun n => ∫ p, IBMActualSimpson.sums (shiftedJet g a 1) T n p * f p
    ∂IBMSourceLaws.jointMeasure) atTop (𝓝 _)
  rw [hfun]
  simpa only [Function.comp_def,innerSL_apply_apply] using h

theorem actual_pairing_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (T : ℝ≥0)
    (F : jointDerivative.domain) :
    Tendsto (fun n => ∫ p, IBMActualSimpson.sums (shiftedJet g a 1) T n p *
      ((F : IntrinsicSpace) : JointL2) p ∂IBMSourceLaws.jointMeasure) atTop
      (𝓝 (inner ℝ (IBMSchwartzHybridReconstruction.integrand g a T) (jointDerivative F) +
        inner ℝ (meanShift g a T) ((F : IntrinsicSpace) : JointL2))) := by
  let f : JointL2 := (F : IntrinsicSpace)
  have hl : inner ℝ f (physicalValue g a T) =
      inner ℝ (IBMSchwartzHybridReconstruction.integrand g a T) (jointDerivative F) +
        inner ℝ (meanShift g a T) f := by
    rw [real_inner_comm]
    have h := native_duality g a T F
    rw [inner_sub_left] at h
    change inner ℝ (physicalValue g a T) f-inner ℝ (meanShift g a T) f = _ at h
    linarith
  simpa only [hl] using pairing_tendsto g a T f

end OperatorDerivativeRewrite.Foundation.IBMSchwartzSimpsonNative
