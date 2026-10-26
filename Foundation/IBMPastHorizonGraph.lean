import Foundation.MonotoneHilbertProjection
import Foundation.IBMPastGraphRegularization
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Actual finite-past IBM derivative graphs in ONE ambient Hilbert space.
Their monotone projections recover the existing canonical adapted regularizers,
and prove strong horizon measurability of BOTH actual inputs and native gradients.
No jointly measurable sample representative or temporal Ito formula is inferred. -/
noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPastHorizonGraph
open OperatorDerivativeRewrite.Foundation
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance : SecondCountableTopology InfiniteGaussian.GaussianVectorL2 :=
  Lp.SecondCountableTopology (E := InfiniteGaussian.CoefficientSpace) (p := 2) (μ := InfiniteGaussian.gaussianProduct)
local instance : SecondCountableTopology IBMIntrinsicOperators.FieldSpace :=
  Lp.SecondCountableTopology (E := InfiniteGaussian.GaussianVectorL2) (p := 2) (μ := InfiniteGaussian.gaussianProduct)
local instance : SecondCountableTopology JointFieldSpace := inferInstance
open IBMPastIntrinsicOperators ScaledGraphResolvent
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable IBMConstructedSources.clockPath_measurable).completeSpace_coe
local instance (T : ℝ≥0) : CompleteSpace (pastSpace T) := (pastSpace_closed T).completeSpace_coe

abbrev Ambient := WithLp 2 (IntrinsicSpace × JointFieldSpace)

def horizonGraph (n : ℕ) (T : ℝ≥0) : ClosedSubmodule ℝ Ambient :=
  ⟨(ClosedOperatorEnergyResolvent.graphSpace (E := IntrinsicSpace) (F := JointFieldSpace) (scale n • jointDerivative)
      (smul_closed (E := IntrinsicSpace) (F := JointFieldSpace) jointDerivative jointDerivative_closed _ (scale_pos n).ne')).toSubmodule ⊓
    (pastSpace T).comap (WithLp.fstL 2 ℝ IntrinsicSpace JointFieldSpace).toLinearMap,
    (ClosedOperatorEnergyResolvent.graphSpace (E := IntrinsicSpace) (F := JointFieldSpace) (scale n • jointDerivative)
      (smul_closed (E := IntrinsicSpace) (F := JointFieldSpace) jointDerivative jointDerivative_closed _ (scale_pos n).ne')).isClosed.inter
        ((pastSpace_closed T).preimage (WithLp.fstL 2 ℝ IntrinsicSpace JointFieldSpace).continuous)⟩

theorem pastSpace_mono : Monotone pastSpace := by
  intro S T hST f hf
  change AEStronglyMeasurable[IBMNaturalFiltrationObstruction.naturalFiltration S]
    (f:JointL2) IBMSourceLaws.jointMeasure at hf
  change AEStronglyMeasurable[IBMNaturalFiltrationObstruction.naturalFiltration T]
    (f:JointL2) IBMSourceLaws.jointMeasure
  exact hf.mono (IBMNaturalFiltrationObstruction.naturalFiltration.mono hST)

theorem horizonGraph_mono (n : ℕ) : Monotone (fun T => (horizonGraph n T).toSubmodule) := by
  intro S T hST z hz
  exact ⟨hz.1,pastSpace_mono hST hz.2⟩

theorem projection_stronglyMeasurable (n : ℕ) (x : Ambient) :
    StronglyMeasurable (fun T => (horizonGraph n T).starProjection x) :=
  MonotoneHilbertProjection.stronglyMeasurable_projection
    (fun T => (horizonGraph n T).toSubmodule) (horizonGraph_mono n) x

theorem mem_horizonGraph (n : ℕ) (T : ℝ≥0) (f : IntrinsicSpace) (g : JointFieldSpace) :
    WithLp.toLp 2 (f,g) ∈ horizonGraph n T ↔
      (f,g) ∈ (scale n • jointDerivative).graph ∧ f ∈ pastSpace T := Iff.rfl

private theorem derivative_smul (a : ℝ) (T : ℝ≥0) :
    ObservableRestriction.derivative (a • jointDerivative) (pastSpace T) = a • pastDerivative T := rfl

attribute [local irreducible] IBMPastIntrinsicOperators.pastDerivative IBMJointIntrinsicDerivative.jointDerivative
attribute [local irreducible] ScaledGraphResolvent.regularize ScaledGraphResolvent.nativeGradient
attribute [local irreducible] LinearPMap.graph horizonGraph

theorem scaled_past_graph (n : ℕ) (T : ℝ≥0) (f : pastSpace T) (g : JointFieldSpace) :
    (f,g) ∈ (scale n • pastDerivative T).graph ↔
      ((f:IntrinsicSpace),g) ∈ (scale n • jointDerivative).graph := by
  have he := congrArg (fun A : pastSpace T →ₗ.[ℝ] JointFieldSpace =>
    (f,g) ∈ A.graph ↔ ((f:IntrinsicSpace),g) ∈ (scale n • jointDerivative).graph)
    (derivative_smul (scale n) T)
  exact Eq.mp he (ObservableRestriction.derivative_graph (scale n • jointDerivative) (pastSpace T) f g)

open IBMPastGraphRegularization

def nativePair (n : ℕ) (T : ℝ≥0) (f : pastSpace T) : Ambient :=
  WithLp.toLp 2 (((regularizer T n f).val:IntrinsicSpace),scale n • gradient T n f)

theorem nativePair_mem (n : ℕ) (T : ℝ≥0) (f : pastSpace T) : nativePair n T f ∈ horizonGraph n T := by
  apply (mem_horizonGraph _ _ _ _).2
  refine ⟨(scaled_past_graph _ _ _ _).1 ?_,(regularizer T n f).property⟩
  unfold IBMPastGraphRegularization.gradient ScaledGraphResolvent.nativeGradient
  unfold IBMPastGraphRegularization.regularizer
  simpa only [LinearPMap.smul_apply] using (scale n • pastDerivative T).mem_graph
    ⟨regularize (pastDerivative T) (pastDerivative_closed T) n f,
      regularize_mem (pastDerivative T) (pastDerivative_closed T) n f⟩

def graphInclusion (T : ℝ≥0) : WithLp 2 (pastSpace T × JointFieldSpace) →ₗᵢ[ℝ] Ambient :=
  LinearIsometry.withLpProdMap (p := 2)
    ({toLinearMap := (pastSpace T).subtype, norm_map' := fun _ => rfl} :
      pastSpace T →ₗᵢ[ℝ] IntrinsicSpace)
    ({toLinearMap := LinearMap.id, norm_map' := fun _ => rfl} :
      JointFieldSpace →ₗᵢ[ℝ] JointFieldSpace)

theorem graph_image (n : ℕ) (T : ℝ≥0) :
    (ClosedOperatorEnergyResolvent.graphSpace (E := pastSpace T) (F := JointFieldSpace) (scale n • pastDerivative T)
      (smul_closed (E := pastSpace T) (F := JointFieldSpace) (pastDerivative T) (pastDerivative_closed T) _ (scale_pos n).ne')).toSubmodule.map
        (graphInclusion T).toLinearMap = (horizonGraph n T).toSubmodule := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    change WithLp.toLp 2 (((WithLp.ofLp z).1.val:IntrinsicSpace),(WithLp.ofLp z).2) ∈ horizonGraph n T
    apply (mem_horizonGraph n T _ _).2
    have hzo : ((WithLp.ofLp z).1,(WithLp.ofLp z).2) ∈ (scale n • pastDerivative T).graph := hz
    exact ⟨(scaled_past_graph n T _ _).1 hzo,(WithLp.ofLp z).1.property⟩
  · intro hw
    have hm := (mem_horizonGraph n T (WithLp.ofLp w).1 (WithLp.ofLp w).2).1 hw
    let f : pastSpace T := ⟨(WithLp.ofLp w).1,hm.2⟩
    refine ⟨WithLp.toLp 2 (f,(WithLp.ofLp w).2),?_,?_⟩
    · exact (scaled_past_graph n T f _).2 hm.1
    · rfl

private theorem product_pairing {X Y : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    (x y : X) (g : Y) (w : WithLp 2 (X × Y)) :
    inner ℝ (WithLp.toLp 2 (x,(0:Y))-WithLp.toLp 2 (y,g)) w =
      inner ℝ (x-y) (WithLp.ofLp w).1-inner ℝ g (WithLp.ofLp w).2 := by
  change inner ℝ (WithLp.toLp 2 (x,(0:Y))-WithLp.toLp 2 (y,g))
    (WithLp.toLp 2 ((WithLp.ofLp w).1,(WithLp.ofLp w).2)) = _
  rw [inner_sub_left,WithLp.prod_inner_apply,WithLp.prod_inner_apply,inner_zero_left,add_zero,inner_sub_left]
  ring

private theorem subspace_pairing {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (U : Submodule ℝ X) (x y z : U) :
    inner ℝ ((x:X)-(y:X)) (z:X) = inner ℝ (x-y) z := rfl

private theorem scalar_pairing {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (a : ℝ) (x y : X) : inner ℝ (a • x) (a • y) = a^2*inner ℝ x y := by
  rw [real_inner_smul_left,inner_smul_right]
  ring

private theorem native_pair_orthogonality (n : ℕ) (T : ℝ≥0) (f : pastSpace T)
    (w : Ambient) (hw : w ∈ horizonGraph n T) :
    inner ℝ (WithLp.toLp 2 ((f.val:IntrinsicSpace),(0:JointFieldSpace))-nativePair n T f) w = 0 := by
  have hwm := (mem_horizonGraph n T (WithLp.ofLp w).1 (WithLp.ofLp w).2).1 hw
  let g : pastSpace T := ⟨(WithLp.ofLp w).1,hwm.2⟩
  have hg := (scaled_past_graph n T g (WithLp.ofLp w).2).2 hwm.1
  obtain ⟨u,hu,hv⟩ := (scale n • pastDerivative T).mem_graph_iff.mp hg
  have hf : (WithLp.ofLp w).1 = (u.val:IntrinsicSpace) := (congrArg Subtype.val hu).symm
  change scale n • pastDerivative T u = (WithLp.ofLp w).2 at hv
  have hadj := congrArg (fun v : pastSpace T => inner ℝ v (u:pastSpace T))
    (native_divergence_correction T n f)
  have hibp := integration_by_parts T ⟨correction T n f,correction_domain T n f⟩ u
  have he : inner ℝ (f-regularizer T n f) (u:pastSpace T) =
      (scale n)^2*inner ℝ (gradient T n f) (pastDerivative T u) := by
    have hh := hadj.symm.trans hibp
    simpa only [IBMPastGraphRegularization.correction,real_inner_smul_left] using hh
  have hp := product_pairing (f.val:IntrinsicSpace) ((regularizer T n f).val:IntrinsicSpace)
    (scale n • gradient T n f) w
  calc
    _ = inner ℝ ((f.val:IntrinsicSpace)-((regularizer T n f).val:IntrinsicSpace)) (WithLp.ofLp w).1 -
        inner ℝ (scale n • gradient T n f) (WithLp.ofLp w).2 := hp
    _ = inner ℝ (f-regularizer T n f) (u:pastSpace T) -
        (scale n)^2*inner ℝ (gradient T n f) (pastDerivative T u) := by
      have hfirst := congrArg (fun z : IntrinsicSpace =>
        inner ℝ ((f.val:IntrinsicSpace)-((regularizer T n f).val:IntrinsicSpace)) z) hf
      have hsecond := congrArg (fun z : JointFieldSpace => inner ℝ (scale n • gradient T n f) z) hv.symm
      exact congrArg₂ (fun a b : ℝ => a-b)
        (hfirst.trans (subspace_pairing (pastSpace T) f (regularizer T n f) u))
        (hsecond.trans (scalar_pairing (X := JointFieldSpace) (scale n) (gradient T n f) (pastDerivative T u)))
    _ = 0 := sub_eq_zero.mpr he

theorem projection_nativePair (n : ℕ) (T : ℝ≥0) (f : pastSpace T) :
    (horizonGraph n T).starProjection (WithLp.toLp 2 ((f.val:IntrinsicSpace),(0:JointFieldSpace))) =
      nativePair n T f :=
  (horizonGraph n T).toSubmodule.eq_starProjection_of_mem_of_inner_eq_zero (nativePair_mem n T f)
    (fun w hw => native_pair_orthogonality n T f w hw)

theorem projected_endpoint_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun T => (horizonGraph n T).starProjection
      (ClosedOperatorEnergyResolvent.input (E := IntrinsicSpace) (F := JointFieldSpace) (intrinsicCurve T))) := by
  borelize Ambient
  have hu : StronglyMeasurable (fun p : Ambient × ℝ≥0 => (horizonGraph n p.2).starProjection p.1) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      (u := fun x : Ambient => fun T : ℝ≥0 => (horizonGraph n T).starProjection x)
      (fun T => (horizonGraph n T).starProjection.continuous) (projection_stronglyMeasurable n)
  have hc : Continuous (fun T =>
      ClosedOperatorEnergyResolvent.input (E := IntrinsicSpace) (F := JointFieldSpace) (intrinsicCurve T)) :=
    (ClosedOperatorEnergyResolvent.input (E := IntrinsicSpace) (F := JointFieldSpace)).continuous.comp
      intrinsicCurve_continuous
  simpa only [Function.comp_def,id] using hu.comp_measurable (hc.measurable.prodMk measurable_id)

theorem nativePair_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun T => nativePair n T (endpoint T)) := by
  have he : (fun T => (horizonGraph n T).starProjection
      (ClosedOperatorEnergyResolvent.input (E := IntrinsicSpace) (F := JointFieldSpace) (intrinsicCurve T))) =
      (fun T => nativePair n T (endpoint T)) := by
    funext T
    exact projection_nativePair n T (endpoint T)
  exact he ▸ projected_endpoint_stronglyMeasurable n

theorem approximation_stronglyMeasurable (n : ℕ) : StronglyMeasurable (fun T => approximation T n) := by
  have hf := (WithLp.fstL 2 ℝ IntrinsicSpace JointFieldSpace).continuous.comp_stronglyMeasurable
    (nativePair_stronglyMeasurable n)
  exact IntrinsicSpace.subtypeL.continuous.comp_stronglyMeasurable hf

theorem gradient_stronglyMeasurable (n : ℕ) :
    StronglyMeasurable (fun T => gradient T n (endpoint T)) := by
  have hf := (WithLp.sndL 2 ℝ IntrinsicSpace JointFieldSpace).continuous.comp_stronglyMeasurable
    (nativePair_stronglyMeasurable n)
  have hg := hf.const_smul ((scale n)⁻¹)
  convert hg using 1
  funext T
  change gradient T n (endpoint T) = (scale n)⁻¹ • (scale n • gradient T n (endpoint T))
  rw [smul_smul,inv_mul_cancel₀ (scale_pos n).ne',one_smul]

end OperatorDerivativeRewrite.Foundation.IBMPastHorizonGraph
