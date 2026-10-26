import Foundation.JointLpRepresentative
import Foundation.IBMPastHorizonGraph

/-! Joint sample representatives of the ACTUAL adapted IBM regularizers and
their original native derivative fields, with L2/AE agreement at EVERY horizon.
Native field coordinates retain their explicit source/clock chart ordering.
No path regularity, simultaneous indistinguishability or temporal Ito law is claimed. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastSampleRealization
open InfiniteGaussian IBMTimeAveragedObservable IBMIntrinsicOperators
open IBMJointIntrinsicDerivative IBMPastGraphRegularization
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : SecondCountableTopology GaussianVectorL2 :=
  Lp.SecondCountableTopology (E := CoefficientSpace) (p := 2) (μ := gaussianProduct)
local instance : SecondCountableTopology FieldSpace :=
  Lp.SecondCountableTopology (E := GaussianVectorL2) (p := 2) (μ := gaussianProduct)

private theorem input_exists (n : ℕ) : ∃ g : ℝ≥0 × IBMSourceLaws.JointSample → ℝ,
    StronglyMeasurable g ∧ ∀ T, approximation T n =ᵐ[IBMSourceLaws.jointMeasure] fun ω => g (T,ω) :=
  JointLpRepresentative.exists_joint_representative _
    (IBMPastHorizonGraph.approximation_stronglyMeasurable n)

def sample (n : ℕ) : ℝ≥0 × IBMSourceLaws.JointSample → ℝ := Classical.choose (input_exists n)

theorem sample_stronglyMeasurable (n : ℕ) : StronglyMeasurable (sample n) :=
  (Classical.choose_spec (input_exists n)).1

theorem sample_ae (n : ℕ) (T : ℝ≥0) :
    approximation T n =ᵐ[IBMSourceLaws.jointMeasure] fun ω => sample n (T,ω) :=
  (Classical.choose_spec (input_exists n)).2 T

theorem sample_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => sample n (T,ω)) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (approximation T n)).ae_eq (sample_ae n T)

theorem sample_past (n : ℕ) (T : ℝ≥0) :
    AEStronglyMeasurable[IBMNaturalFiltrationObstruction.naturalFiltration T]
      (fun ω => sample n (T,ω)) IBMSourceLaws.jointMeasure :=
  (approximation_past T n).congr (sample_ae n T)

theorem sample_toLp (n : ℕ) (T : ℝ≥0) :
    (sample_memLp n T).toLp (fun ω => sample n (T,ω)) = approximation T n := by
  apply Lp.ext
  exact (MemLp.coeFn_toLp (sample_memLp n T)).trans (sample_ae n T).symm

theorem sample_L2_tendsto (T : ℝ≥0) :
    Tendsto (fun n => (sample_memLp n T).toLp (fun ω => sample n (T,ω))) atTop
      (𝓝 (intrinsicCurve T : JointL2)) := by
  simpa only [sample_toLp] using actual_endpoint_tendsto T

/-- A common null set is available for any specified COUNTABLE family of horizons. -/
theorem sample_countable_ae {ι : Type*} [Countable ι] (times : ι → ℝ≥0) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ∀ n : ℕ, ∀ j : ι,
      approximation (times j) n ω = sample n (times j,ω) := by
  exact ae_all_iff.mpr fun n => ae_all_iff.mpr fun j => sample_ae n (times j)

/-- Uncurry the stored native channel without changing its Gaussian coordinate chart. -/
def channelField (n : ℕ) (T : ℝ≥0) (i : Fin 2) :
    Lp CoefficientSpace 2 IBMSourceLaws.jointMeasure :=
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm (gradient T n (endpoint T) i)

theorem channelField_stronglyMeasurable (n : ℕ) (i : Fin 2) :
    StronglyMeasurable (fun T => channelField n T i) := by
  have h := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 2 => FieldSpace) i).continuous
    |>.comp_stronglyMeasurable
    (IBMPastHorizonGraph.gradient_stronglyMeasurable n)
  exact (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm.continuous
    |>.comp_stronglyMeasurable h

private theorem field_exists (n : ℕ) (i : Fin 2) :
    ∃ g : ℝ≥0 × IBMSourceLaws.JointSample → CoefficientSpace, StronglyMeasurable g ∧
      ∀ T, channelField n T i =ᵐ[IBMSourceLaws.jointMeasure] fun ω => g (T,ω) := by
  borelize ↥CoefficientSpace
  exact JointLpRepresentative.exists_joint_representative _ (channelField_stronglyMeasurable n i)

def channelSample (n : ℕ) (i : Fin 2) : ℝ≥0 × IBMSourceLaws.JointSample → CoefficientSpace :=
  Classical.choose (field_exists n i)

theorem channelSample_stronglyMeasurable (n : ℕ) (i : Fin 2) :
    StronglyMeasurable (channelSample n i) := (Classical.choose_spec (field_exists n i)).1

theorem channelSample_ae (n : ℕ) (T : ℝ≥0) (i : Fin 2) :
    channelField n T i =ᵐ[IBMSourceLaws.jointMeasure] fun ω => channelSample n i (T,ω) :=
  (Classical.choose_spec (field_exists n i)).2 T

theorem channelSample_memLp (n : ℕ) (T : ℝ≥0) (i : Fin 2) :
    MemLp (fun ω => channelSample n i (T,ω)) 2 IBMSourceLaws.jointMeasure :=
  (Lp.memLp (channelField n T i)).ae_eq (channelSample_ae n T i)

/-- The original stored channel is recovered as nested L2 sections at EVERY T. -/
theorem channelSample_sections (n : ℕ) (T : ℝ≥0) (i : Fin 2) :
    ∀ᵐ x ∂gaussianProduct, gradient T n (endpoint T) i x =ᵐ[gaussianProduct]
      fun y => channelSample n i (T,(x,y)) := by
  have h := ProductL2Curry.curryEquiv_symm_coeFn gaussianProduct gaussianProduct
    (gradient T n (endpoint T) i)
  have ha := Measure.ae_ae_of_ae_prod (channelSample_ae n T i)
  filter_upwards [h,ha] with x hx hax
  exact hx.trans hax

/-- In physical (scenery,clock) order, the source channel uses its swapped chart. -/
def sourceSample (n : ℕ) (z : ℝ≥0 × IBMSourceLaws.JointSample) : CoefficientSpace :=
  channelSample n 0 (z.1,(z.2.2,z.2.1))

def clockSample (n : ℕ) : ℝ≥0 × IBMSourceLaws.JointSample → CoefficientSpace := channelSample n 1

theorem sourceSample_stronglyMeasurable (n : ℕ) : StronglyMeasurable (sourceSample n) :=
  (channelSample_stronglyMeasurable n 0).comp_measurable
    (measurable_fst.prodMk
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd)))

theorem clockSample_stronglyMeasurable (n : ℕ) : StronglyMeasurable (clockSample n) :=
  channelSample_stronglyMeasurable n 1

theorem sourceSample_sections (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ clock ∂gaussianProduct, gradient T n (endpoint T) 0 clock =ᵐ[gaussianProduct]
      fun scenery => sourceSample n (T,(scenery,clock)) :=
  channelSample_sections n T 0

theorem clockSample_sections (n : ℕ) (T : ℝ≥0) :
    ∀ᵐ scenery ∂gaussianProduct, gradient T n (endpoint T) 1 scenery =ᵐ[gaussianProduct]
      fun clock => clockSample n (T,(scenery,clock)) :=
  channelSample_sections n T 1

theorem sourceSample_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => sourceSample n (T,ω)) 2 IBMSourceLaws.jointMeasure :=
  (channelSample_memLp n T 0).comp_measurePreserving Measure.measurePreserving_swap

theorem clockSample_memLp (n : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => clockSample n (T,ω)) 2 IBMSourceLaws.jointMeasure :=
  channelSample_memLp n T 1

end OperatorDerivativeRewrite.Foundation.IBMPastSampleRealization
