import Foundation.GaussianProductDerivative
import Foundation.BochnerLinearIsometry

/-! Actual Brownian-time coordinates for coefficient-valued derivative fields.
The time embedding need not be onto. Reconstruction is proved on its range;
no coefficient directions are silently identified or discarded. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianDerivativeTimeCoordinates
open InfiniteGaussian GaussianTimeHilbert GaussianTimeProductL2 GaussianProductDerivative
open SeparableHilbertEmbedding GaussianTimeDivergence
attribute [local instance] timeHilbert_secondCountable coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def timeProjection : CoefficientSpace →L[ℝ] TimeHilbert :=
  (hilbertEmbedding TimeHilbert).toContinuousLinearMap.adjoint

theorem timeProjection_embedding (a : TimeHilbert) :
    timeProjection (hilbertEmbedding TimeHilbert a) = a := by
  exact congrArg (fun L : TimeHilbert →L[ℝ] TimeHilbert => L a)
    (hilbertEmbedding TimeHilbert).adjoint_comp_self

abbrev TimeValuedFields := Lp TimeHilbert 2 timeProbability
abbrev twoTimeProbability := timeProbability.prod (volume : Measure ℝ)
abbrev TwoTimeL2 := Lp ℝ 2 twoTimeProbability

def embedTimeField : TimeValuedFields →ₗᵢ[ℝ] ProductDerivativeL2 :=
  BochnerLinearIsometry.lift timeProbability (hilbertEmbedding TimeHilbert)

def projectTimeField : ProductDerivativeL2 →L[ℝ] TimeValuedFields :=
  timeProjection.compLpL 2 timeProbability

theorem projectTimeField_coeFn (v : ProductDerivativeL2) :
    projectTimeField v =ᵐ[timeProbability] fun z => timeProjection (v z) :=
  timeProjection.coeFn_compLp v

theorem projectTimeField_embed (v : TimeValuedFields) :
    projectTimeField (embedTimeField v) = v := by
  apply Lp.ext
  filter_upwards [projectTimeField_coeFn (embedTimeField v),
    BochnerLinearIsometry.lift_coeFn timeProbability (hilbertEmbedding TimeHilbert) v]
    with z hp he
  change embedTimeField v z = hilbertEmbedding TimeHilbert (v z) at he
  rw [hp, he, timeProjection_embedding]

/-- Coordinates are ordered `((integration time, sample), derivative time)`. -/
def timeCoordinates : ProductDerivativeL2 →L[ℝ] TwoTimeL2 :=
  let e : TwoTimeL2 ≃ₗᵢ[ℝ] TimeValuedFields :=
    ProductL2Curry.curryEquiv timeProbability volume
  e.symm.toLinearIsometry.toContinuousLinearMap.comp projectTimeField

def reconstruct : TwoTimeL2 →ₗᵢ[ℝ] ProductDerivativeL2 :=
  embedTimeField.comp (ProductL2Curry.curryEquiv timeProbability volume).toLinearIsometry

theorem timeCoordinates_reconstruct (v : TwoTimeL2) : timeCoordinates (reconstruct v) = v := by
  change (ProductL2Curry.curryEquiv timeProbability volume).symm
    (projectTimeField (embedTimeField ((ProductL2Curry.curryEquiv timeProbability volume) v))) = v
  rw [projectTimeField_embed, LinearIsometryEquiv.symm_apply_apply]

theorem timeCoordinates_coeFn (v : ProductDerivativeL2) :
    ∀ᵐ z ∂timeProbability, timeProjection (v z) =ᵐ[volume]
      fun s => timeCoordinates v (z, s) := by
  filter_upwards [ProductL2Curry.curryEquiv_symm_coeFn timeProbability volume
    (projectTimeField v), projectTimeField_coeFn v] with z hz hp
  rwa [hp] at hz

/-- The range condition is essential: outside this range time coordinates are only a projection. -/
theorem reconstruct_timeCoordinates (v : ProductDerivativeL2)
    (hv : v ∈ embedTimeField.toLinearMap.range) : reconstruct (timeCoordinates v) = v := by
  obtain ⟨w, rfl⟩ := hv
  change embedTimeField ((ProductL2Curry.curryEquiv timeProbability volume)
    ((ProductL2Curry.curryEquiv timeProbability volume).symm
      (projectTimeField (embedTimeField w)))) = embedTimeField w
  rw [LinearIsometryEquiv.apply_symm_apply, projectTimeField_embed]

theorem timeCoordinates_norm (v : ProductDerivativeL2)
    (hv : v ∈ embedTimeField.toLinearMap.range) : ‖timeCoordinates v‖ = ‖v‖ := by
  rw [← reconstruct.norm_map, reconstruct_timeCoordinates v hv]

/-- Actual projection of the genuine polynomial gradient, with no independent derivative data. -/
theorem past_gradient_timeProjection {n : ℕ} (r : Fin n → ℝ≥0)
    (p : MvPolynomial (Fin n) ℝ) :
    (fun ω => timeProjection (polynomialDerivative (pastCoefficient r p) ω)) =ᵐ[gaussianProduct]
      fun ω => ∑ i, MvPolynomial.eval (fun j => GaussianTimeProcess.process (r j) ω)
        (MvPolynomial.pderiv i p) • timeVector (r i) := by
  change (fun ω => timeProjection (polynomialDerivative
    ⟨isonormalCylinderL2 (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p,
      _⟩ ω)) =ᵐ[_] _
  rw [polynomialDerivative_on_cylinder]
  filter_upwards [isonormalCylinderGradientL2_coeFn
    (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p] with ω hω
  rw [hω]
  simp only [isonormalCylinderGradient, map_sum, map_smul, timeProjection_embedding]
  rfl

theorem past_gradient_reconstruction {n : ℕ} (r : Fin n → ℝ≥0)
    (p : MvPolynomial (Fin n) ℝ) :
    (fun ω => hilbertEmbedding TimeHilbert
      (timeProjection (polynomialDerivative (pastCoefficient r p) ω))) =ᵐ[gaussianProduct]
      polynomialDerivative (pastCoefficient r p) := by
  have he : polynomialDerivative (pastCoefficient r p) = isonormalCylinderGradientL2
      (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p :=
    polynomialDerivative_on_cylinder _ _
  rw [he]
  filter_upwards [isonormalCylinderGradientL2_coeFn
    (fun i => hilbertEmbedding TimeHilbert (timeVector (r i))) p] with ω hω
  rw [hω]
  simp only [isonormalCylinderGradient, map_sum, map_smul, timeProjection_embedding]

end OperatorDerivativeRewrite.Foundation.GaussianDerivativeTimeCoordinates
