import Foundation.IBMQuadraticClockMartingale

/-! An actual clock Stein identity on the full original native derivative domain. -/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockSteinIdentity
open IBMTimeAveragedObservable IBMJointIntrinsicDerivative IBMIntrinsicChainRule
open IBMClockLinearDivergence IBMNativeFieldMultiplier
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
local instance : CompleteSpace IntrinsicSpace :=
  (IBMConditionalObservable.observableSpace_isClosed _ _
    IBMConstructedSources.sceneryPath_measurable
    IBMConstructedSources.clockPath_measurable).completeSpace_coe
set_option backward.isDefEq.respectTransparency false

def clockGradient (f : jointDerivative.domain) : JointVectorL2 :=
  uncurryField (jointDerivative f 1)

def steinFunction (T : ℝ≥0) (f : jointDerivative.domain)
    (ω : IBMSourceLaws.JointSample) : ℝ :=
  IBMConstructedSources.clockPath ω.2 T * inner ℝ (clockGradient f ω) (timeDirection T)

theorem stein_ae (T : ℝ≥0) (f : jointDerivative.domain) :
    (fun ω => inner ℝ
      (uncurryField (nativeField (timeDirection T) (timeDirection T) 1) ω)
      (clockGradient f ω)) =ᵐ[IBMSourceLaws.jointMeasure] steinFunction T f := by
  filter_upwards [time_field_ae T] with ω hω
  rw [hω,real_inner_smul_left,real_inner_comm]
  rfl

theorem stein_integrable (T : ℝ≥0) (f : jointDerivative.domain) :
    Integrable (steinFunction T f) IBMSourceLaws.jointMeasure :=
  (L2.integrable_inner
    (uncurryField (nativeField (timeDirection T) (timeDirection T) 1))
    (clockGradient f)).congr (stein_ae T f)

theorem field_pairing (T : ℝ≥0) (f : jointDerivative.domain) :
    inner ℝ (nativeField (timeDirection T) (timeDirection T)) (jointDerivative f) =
      ∫ ω, steinFunction T f ω ∂IBMSourceLaws.jointMeasure := by
  have he := IBMObservableClockKernel.coordinate_inner
    (nativeField (timeDirection T) (timeDirection T)) (jointDerivative f)
  have hz : coordinate 0 (nativeField (timeDirection T) (timeDirection T) 0) = 0 :=
    (coordinate 0).map_zero
  rw [hz,inner_zero_left,zero_add] at he
  exact he.trans ((L2.inner_def _ _).trans (integral_congr_ae (stein_ae T f)))

theorem quadratic_integrable (T : ℝ≥0) (f : jointDerivative.domain) :
    Integrable (fun ω => (((f : IntrinsicSpace) : JointL2) ω) *
      ((IBMConstructedSources.clockPath ω.2 T)^2 - T)) IBMSourceLaws.jointMeasure := by
  apply (L2.integrable_inner (IBMEvenClockProjection.clockQuadratic T)
    ((f : IntrinsicSpace) : JointL2)).congr
  filter_upwards [IBMEvenClockProjection.clockQuadratic_ae T] with ω hω
  rw [hω,Real.inner_apply,mul_comm]

theorem quadratic_inner (T : ℝ≥0) (F : JointL2) :
    inner ℝ (IBMEvenClockProjection.clockQuadratic T) F =
      ∫ ω, F ω * ((IBMConstructedSources.clockPath ω.2 T)^2 - T)
        ∂IBMSourceLaws.jointMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [IBMEvenClockProjection.clockQuadratic_ae T] with ω hω
  rw [hω,Real.inner_apply,mul_comm]

theorem integration_by_parts (T : ℝ≥0) (f : jointDerivative.domain) :
    (∫ ω, (((f : IntrinsicSpace) : JointL2) ω) *
      ((IBMConstructedSources.clockPath ω.2 T)^2 - T) ∂IBMSourceLaws.jointMeasure) =
    ∫ ω, steinFunction T f ω ∂IBMSourceLaws.jointMeasure := by
  have he := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense
    ⟨nativeField (timeDirection T) (timeDirection T),native_mem _ _⟩ f
  rw [native_value,time_output] at he
  have hp := IntrinsicSpace.inner_orthogonalProjectionOnto_eq_of_mem_right
    (f : IntrinsicSpace) (IBMEvenClockProjection.clockQuadratic T)
  exact (quadratic_inner T ((f : IntrinsicSpace) : JointL2)).symm.trans
    (hp.symm.trans (he.trans (field_pairing T f)))

theorem zero_clock_gradient_pairing (T : ℝ≥0) (f : jointDerivative.domain)
    (hf : clockGradient f = 0) :
    (∫ ω, (((f : IntrinsicSpace) : JointL2) ω) *
      ((IBMConstructedSources.clockPath ω.2 T)^2 - T) ∂IBMSourceLaws.jointMeasure) = 0 := by
  rw [integration_by_parts]
  apply integral_eq_zero_of_ae
  filter_upwards [Lp.coeFn_zero InfiniteGaussian.CoefficientSpace 2
    IBMSourceLaws.jointMeasure] with ω hω
  change (0 : JointVectorL2) ω = (0 : InfiniteGaussian.CoefficientSpace) at hω
  change IBMConstructedSources.clockPath ω.2 T *
    inner ℝ (clockGradient f ω) (timeDirection T) = 0
  rw [hf,hω,inner_zero_left,mul_zero]

def nonlinearFunction (T : ℝ≥0) (f : jointDerivative.domain) (dφ : ℝ → ℝ)
    (ω : IBMSourceLaws.JointSample) : ℝ :=
  IBMConstructedSources.clockPath ω.2 T * dφ (((f : IntrinsicSpace) : JointL2) ω) *
    inner ℝ (clockGradient f ω) (timeDirection T)

theorem chain_stein_ae (T : ℝ≥0) (f F : jointDerivative.domain) (dφ : ℝ → ℝ)
    (hF : clockGradient F =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => dφ (((f : IntrinsicSpace) : JointL2) ω) • clockGradient f ω) :
    steinFunction T F =ᵐ[IBMSourceLaws.jointMeasure] nonlinearFunction T f dφ := by
  filter_upwards [hF] with ω hω
  change IBMConstructedSources.clockPath ω.2 T *
    inner ℝ (clockGradient F ω) (timeDirection T) = _
  rw [hω,real_inner_smul_left]
  exact (mul_assoc _ _ _).symm

theorem chain_integration_by_parts (T : ℝ≥0) (f : jointDerivative.domain)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (B : ℝ) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    Integrable (fun ω => φ (((f : IntrinsicSpace) : JointL2) ω) *
      ((IBMConstructedSources.clockPath ω.2 T)^2 - T)) IBMSourceLaws.jointMeasure ∧
    Integrable (nonlinearFunction T f dφ) IBMSourceLaws.jointMeasure ∧
    (∫ ω, φ (((f : IntrinsicSpace) : JointL2) ω) *
      ((IBMConstructedSources.clockPath ω.2 T)^2 - T) ∂IBMSourceLaws.jointMeasure) =
    ∫ ω, nonlinearFunction T f dφ ω ∂IBMSourceLaws.jointMeasure := by
  obtain ⟨F,hF,hcF,_,_⟩ := IBMIntrinsicUnboundedChain.unbounded_chain f φ dφ hd hc B hB
  have hl : (fun ω => (((F : IntrinsicSpace) : JointL2) ω) *
      ((IBMConstructedSources.clockPath ω.2 T)^2 - T)) =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => φ (((f : IntrinsicSpace) : JointL2) ω) *
        ((IBMConstructedSources.clockPath ω.2 T)^2 - T) :=
    hF.mono fun ω hω => congrArg (fun x : ℝ => x *
      ((IBMConstructedSources.clockPath ω.2 T)^2 - T)) hω
  have hr := chain_stein_ae T f F dφ hcF
  exact ⟨(quadratic_integrable T F).congr hl,(stein_integrable T F).congr hr,
    (integral_congr_ae hl).symm.trans
      ((integration_by_parts T F).trans (integral_congr_ae hr))⟩

theorem exists_nonzero_stein (T : ℝ≥0) (hT : 0 < T) :
    ∃ f : jointDerivative.domain,
      (∫ ω, steinFunction T f ω ∂IBMSourceLaws.jointMeasure) ≠ 0 := by
  by_contra! hn
  apply output_ne_zero T hT
  apply jointDerivative_dense.eq_zero_of_inner_left ℝ
  intro F hF
  let f : jointDerivative.domain := ⟨F,hF⟩
  have he := jointDerivative.adjoint_isFormalAdjoint jointDerivative_dense
    ⟨nativeField (timeDirection T) (timeDirection T),native_mem _ _⟩ f
  rw [native_value] at he
  exact he.trans ((field_pairing T f).trans (hn f))

theorem exists_informative_clock_gradient (T : ℝ≥0) (hT : 0 < T) :
    ∃ f : jointDerivative.domain, clockGradient f ≠ 0 ∧
      (∫ ω, steinFunction T f ω ∂IBMSourceLaws.jointMeasure) ≠ 0 := by
  obtain ⟨f,hf⟩ := exists_nonzero_stein T hT
  refine ⟨f,?_,hf⟩
  intro hz
  have he := zero_clock_gradient_pairing T f hz
  rw [integration_by_parts] at he
  exact hf he

end OperatorDerivativeRewrite.Foundation.IBMClockSteinIdentity
