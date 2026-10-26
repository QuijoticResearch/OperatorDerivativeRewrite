import Foundation.IBMPastTimeGradient

/-! Actual original-space coefficient-valued sample realizations of the native
two-source temporal fields. The source chart swap remains explicit. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMNativeFieldSamples
open InfiniteGaussian IBMIntrinsicOperators IBMJointIntrinsicDerivative
open IBMPastSampleRealization IBMPastTimeGradient IBMClockOverlapEnergy
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : SecondCountableTopology GaussianVectorL2 :=
  Lp.SecondCountableTopology (E := CoefficientSpace) (p := 2) (μ := gaussianProduct)

def channelMap (i : Fin 2) :
    JointFieldSpace →L[ℝ] Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure :=
  let J :=
    (ProductL2Curry.curryEquiv (E := CoefficientSpace) gaussianProduct gaussianProduct).symm
  J.toLinearIsometry.toContinuousLinearMap.comp
    (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 2 => FieldSpace) i)

def curve (n : ℕ) (i : Fin 2) (t : ℝ) : Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure :=
  channelMap i (field n t)

theorem curve_stronglyMeasurable (n : ℕ) (i : Fin 2) : StronglyMeasurable (curve n i) :=
  (channelMap i).continuous.comp_stronglyMeasurable (field_stronglyMeasurable n)

theorem curve_memLp (n : ℕ) (i : Fin 2) (H : ℝ) : MemLp (curve n i) 2 (window H) :=
  (field_memLp n H).continuousLinearMap_comp (channelMap i)

def nativeSample (n : ℕ) (i : Fin 2) (z : ℝ × IBMSourceLaws.JointSample) : CoefficientSpace :=
  channelSample n i (z.1.toNNReal,z.2)

theorem nativeSample_stronglyMeasurable (n : ℕ) (i : Fin 2) :
    StronglyMeasurable (nativeSample n i) :=
  (channelSample_stronglyMeasurable n i).comp_measurable
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)

theorem curve_ae (n : ℕ) (i : Fin 2) (t : ℝ) :
    curve n i t =ᵐ[IBMSourceLaws.jointMeasure] fun ω => nativeSample n i (t,ω) :=
  channelSample_ae n t.toNNReal i

def timeClass (n : ℕ) (i : Fin 2) (H : ℝ) :
    Lp (Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure) 2 (window H) :=
  (curve_memLp n i H).toLp (curve n i)

def sampleClass (n : ℕ) (i : Fin 2) (H : ℝ) :
    Lp CoefficientSpace 2 ((window H).prod IBMSourceLaws.jointMeasure) :=
  (ProductL2Curry.curryEquiv (E := CoefficientSpace) (window H) IBMSourceLaws.jointMeasure).symm
    (timeClass n i H)

theorem sampleClass_ae (n : ℕ) (i : Fin 2) (H : ℝ) :
    sampleClass n i H =ᵐ[(window H).prod IBMSourceLaws.jointMeasure] nativeSample n i := by
  borelize ↥CoefficientSpace
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (Lp.stronglyMeasurable (sampleClass n i H)).measurable
    (nativeSample_stronglyMeasurable n i).measurable)).mpr
  filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn (window H) IBMSourceLaws.jointMeasure
    (timeClass n i H),MemLp.coeFn_toLp (curve_memLp n i H)] with t hc ht
  change timeClass n i H t = curve n i t at ht
  rw [ht] at hc
  exact hc.symm.trans (curve_ae n i t)

theorem nativeSample_memLp (n : ℕ) (i : Fin 2) (H : ℝ) :
    MemLp (nativeSample n i) 2 ((window H).prod IBMSourceLaws.jointMeasure) :=
  (Lp.memLp (sampleClass n i H)).ae_eq (sampleClass_ae n i H)

theorem nativeSample_columns_integrable (n : ℕ) (i : Fin 2) (H : ℝ) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      Integrable (fun t => nativeSample n i (t,ω)) (window H) :=
  ((nativeSample_memLp n i H).integrable (by norm_num)).prod_left_ae

def sourceSample (n : ℕ) (z : ℝ × IBMSourceLaws.JointSample) : CoefficientSpace :=
  nativeSample n 0 (z.1,(z.2.2,z.2.1))
def clockSample (n : ℕ) : ℝ × IBMSourceLaws.JointSample → CoefficientSpace := nativeSample n 1

theorem sourceSample_memLp (n : ℕ) (H : ℝ) :
    MemLp (sourceSample n) 2 ((window H).prod IBMSourceLaws.jointMeasure) :=
  by
    have hid : MeasurePreserving (id : ℝ → ℝ) (window H) (window H) :=
      ⟨measurable_id,Measure.map_id⟩
    exact (nativeSample_memLp n 0 H).comp_measurePreserving
      (hid.prod Measure.measurePreserving_swap)

theorem clockSample_memLp (n : ℕ) (H : ℝ) :
    MemLp (clockSample n) 2 ((window H).prod IBMSourceLaws.jointMeasure) := nativeSample_memLp n 1 H

theorem sourceSample_columns_integrable (n : ℕ) (H : ℝ) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      Integrable (fun t => sourceSample n (t,ω)) (window H) :=
  ((sourceSample_memLp n H).integrable (by norm_num)).prod_left_ae

theorem clockSample_columns_integrable (n : ℕ) (H : ℝ) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure,
      Integrable (fun t => clockSample n (t,ω)) (window H) :=
  ((clockSample_memLp n H).integrable (by norm_num)).prod_left_ae

def integratedChannel (n : ℕ) (i : Fin 2) (H : ℝ) :
    Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure := channelMap i (integratedField n H)

theorem integratedChannel_eq (n : ℕ) (i : Fin 2) (H : ℝ) :
    integratedChannel n i H = ∫ t, curve n i t ∂window H :=
  ((channelMap i).integral_comp_comm ((field_memLp n H).integrable (by norm_num))).symm

private def coordinate (k : ℕ) : CoefficientSpace →L[ℝ] ℝ := lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 k

/-- Full coefficient-space equality, using a COMMON null set for its countably
many coordinates. This is not merely a list of unrelated scalar identities. -/
theorem integratedChannel_ae (n : ℕ) (i : Fin 2) (H : ℝ) :
    integratedChannel n i H =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ∫ t, nativeSample n i (t,ω) ∂window H := by
  have hc : Integrable (curve n i) (window H) := (curve_memLp n i H).integrable (by norm_num)
  have hk (k : ℕ) : (fun ω => coordinate k (integratedChannel n i H ω))
      =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ∫ t, coordinate k (nativeSample n i (t,ω)) ∂window H := by
    let M : Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure →L[ℝ]
        Lp ℝ 2 IBMSourceLaws.jointMeasure := (coordinate k).compLpL 2 IBMSourceLaws.jointMeasure
    have hs : ∀ᵐ t ∂window H, M (curve n i t) =ᵐ[IBMSourceLaws.jointMeasure]
        fun ω => coordinate k (nativeSample n i (t,ω)) :=
      Eventually.of_forall fun t => by
        filter_upwards [(coordinate k).coeFn_compLp (curve n i t),curve_ae n i t]
          with ω hm hω
        exact hm.trans (congrArg (coordinate k) hω)
    have hf := BochnerL2RepresentativeFubini.integral_coeFn_ae
      (fun t => M (curve n i t)) (M.integrable_comp hc)
      (fun z => coordinate k (nativeSample n i z))
      ((coordinate k).continuous.comp_stronglyMeasurable
        (nativeSample_stronglyMeasurable n i)).aestronglyMeasurable hs
    have he : (∫ t, M (curve n i t) ∂window H) = M (integratedChannel n i H) := by
      rw [integratedChannel_eq]
      exact M.integral_comp_comm hc
    rw [he] at hf
    filter_upwards [(coordinate k).coeFn_compLp (integratedChannel n i H),hf] with ω hm hω
    exact hm.symm.trans hω
  filter_upwards [ae_all_iff.mpr hk,nativeSample_columns_integrable n i H] with ω hω hi
  apply lp.ext
  funext k
  exact (hω k).trans ((coordinate k).integral_comp_comm hi)

theorem nativeSample_integral_memLp (n : ℕ) (i : Fin 2) (H : ℝ) :
    MemLp (fun ω => ∫ t, nativeSample n i (t,ω) ∂window H) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (integratedChannel n i H)).ae_eq (integratedChannel_ae n i H)

theorem sourceSample_integral_memLp (n : ℕ) (H : ℝ) :
    MemLp (fun ω => ∫ t, sourceSample n (t,ω) ∂window H) 2 IBMSourceLaws.jointMeasure :=
  (nativeSample_integral_memLp n 0 H).comp_measurePreserving Measure.measurePreserving_swap

theorem clockSample_integral_memLp (n : ℕ) (H : ℝ) :
    MemLp (fun ω => ∫ t, clockSample n (t,ω) ∂window H) 2 IBMSourceLaws.jointMeasure :=
  nativeSample_integral_memLp n 1 H

theorem integrated_native_sections (n : ℕ) (i : Fin 2) (H : ℝ) :
    ∀ᵐ x ∂gaussianProduct, integratedField n H i x =ᵐ[gaussianProduct]
      fun y => ∫ t, nativeSample n i (t,(x,y)) ∂window H := by
  have h := ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct
    (integratedField n H i)
  have ha := Measure.ae_ae_of_ae_prod (integratedChannel_ae n i H)
  filter_upwards [h,ha] with x hx hax
  exact hx.trans hax

theorem integrated_source_sections (n : ℕ) (H : ℝ) :
    ∀ᵐ clock ∂gaussianProduct, integratedField n H 0 clock =ᵐ[gaussianProduct]
      fun scenery => ∫ t, sourceSample n (t,(scenery,clock)) ∂window H :=
  integrated_native_sections n 0 H

theorem integrated_clock_sections (n : ℕ) (H : ℝ) :
    ∀ᵐ scenery ∂gaussianProduct, integratedField n H 1 scenery =ᵐ[gaussianProduct]
      fun clock => ∫ t, clockSample n (t,(scenery,clock)) ∂window H :=
  integrated_native_sections n 1 H

end OperatorDerivativeRewrite.Foundation.IBMNativeFieldSamples
