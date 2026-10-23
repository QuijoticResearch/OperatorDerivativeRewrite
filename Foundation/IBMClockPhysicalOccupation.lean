import Foundation.IBMPhysicalNoiseClock
import Foundation.IBMClockAverageGraph
import Foundation.ClosedOperatorWeakGraphLimit
import Foundation.BochnerLinearIsometry
import Foundation.GaussianClockBochnerContraction

/-! Physical spatial L2 kernels for directional clock derivatives of the
actual linear IBM time average. The kernels are random in the clock sample;
their source white-noise realizations are exact. No strong convergence of
occupation approximants or nonlinear clock gradients is asserted. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMClockPhysicalOccupation
open InfiniteGaussian IBMFirstSourceClockGraph IBMClockAverageGraph
open IBMPhysicalNoiseRealization IBMPhysicalNoiseClock GaussianTimeHilbert
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
attribute [local instance] GaussianTimeHilbert.timeHilbert_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩

def contraction (h : CoefficientSpace) : VectorSpace →L[ℝ] ScalarSpace :=
  ((innerSL ℝ h).compLpL 2 gaussianProduct).compLpL 2 gaussianProduct

def directional (h : CoefficientSpace) : VectorSpace →L[ℝ] ScalarSpace :=
  flip.toContinuousLinearMap.comp (contraction h)

def noiseLift : Lp TimeHilbert 2 gaussianProduct →ₗᵢ[ℝ] ScalarSpace :=
  BochnerLinearIsometry.lift gaussianProduct physicalNoise

def recover : ScalarSpace →L[ℝ] Lp TimeHilbert 2 gaussianProduct :=
  kernelPullback.compLpL 2 gaussianProduct

def physicalProjection : ScalarSpace →L[ℝ] ScalarSpace :=
  noiseLift.toContinuousLinearMap.comp recover

theorem recover_noiseLift (u : Lp TimeHilbert 2 gaussianProduct) :
    recover (noiseLift u) = u := by
  apply Lp.ext
  filter_upwards [kernelPullback.coeFn_compLpL (noiseLift u),
    BochnerLinearIsometry.lift_coeFn gaussianProduct physicalNoise u] with Y hr hn
  change recover (noiseLift u) Y = kernelPullback (noiseLift u Y) at hr
  change noiseLift u Y = physicalNoise (u Y) at hn
  rw [hr, hn, kernelPullback_noise]

theorem contraction_gradientMap (h k : CoefficientSpace) (u : ScalarSpace) :
    contraction h (gradientMap k u) = inner ℝ h k • u := by
  apply Lp.ext
  filter_upwards [((innerSL ℝ h).compLpL 2 gaussianProduct).coeFn_compLpL (gradientMap k u),
    (IBMClockAverageCandidate.tensorBilinear k).coeFn_compLpL u,
    Lp.coeFn_smul (inner ℝ h k) u] with X hc hg hs
  change contraction h (gradientMap k u) X =
    (innerSL ℝ h).compLpL 2 gaussianProduct (gradientMap k u X) at hc
  change gradientMap k u X = IBMClockAverageCandidate.tensorBilinear k (u X) at hg
  rw [hc, hg, IBMClockAverageCandidate.tensorBilinear_eq, hs]
  change (innerSL ℝ h).compLpL 2 gaussianProduct (scalarTensor k (u X)) =
    inner ℝ h k • u X
  apply Lp.ext
  filter_upwards [(innerSL ℝ h).coeFn_compLpL (scalarTensor k (u X)),
    scalarTensor_coeFn k (u X), Lp.coeFn_smul (inner ℝ h k) (u X)] with Y hc ht hs
  rw [hc, ht, hs]
  simp only [innerSL_apply_apply, real_inner_smul_right, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem directional_clockGradient (h : CoefficientSpace) (n : ℕ) (t : ℝ≥0) :
    directional h (clockGradient n t) =
      inner ℝ h (IBMClockAverageCandidate.direction t) • signedSource n t := by
  change flip (contraction h (gradientMap _ (flip (signedSource n t)))) = _
  rw [contraction_gradientMap, map_smul]
  congr 1
  exact GaussianClockBochnerContraction.flip_involution gaussianProduct _

theorem sourceColumn_physical (n : ℕ) (r : ℝ) :
    physicalNoise (IBMPhysicalNoiseCalculus.convolutionKernel
      (deriv (IBMMollifier.kernel n)) r) = IBMClockAverageCandidate.sourceColumn n r := by
  change firstChaosEmbedding (physicalToCoefficient _) = firstChaosEmbedding _
  congr 1
  exact IBMPhysicalNoiseCalculus.triple_coefficient_physical n r 1

theorem signedSource_physical (n : ℕ) (t : ℝ≥0) :
    physicalProjection (signedSource n t) = signedSource n t := by
  apply Lp.ext
  filter_upwards [BochnerLinearIsometry.lift_coeFn gaussianProduct physicalNoise
      (recover (signedSource n t)), kernelPullback.coeFn_compLpL (signedSource n t),
    signedSource_ae n t] with Y hn hr hs
  change physicalProjection (signedSource n t) Y =
    physicalNoise (recover (signedSource n t) Y) at hn
  change recover (signedSource n t) Y = kernelPullback (signedSource n t Y) at hr
  rw [hn, hr, hs]
  change physicalNoise (kernelPullback (_ • IBMClockAverageCandidate.sourceColumn n _)) =
    _ • IBMClockAverageCandidate.sourceColumn n _
  rw [map_smul, map_smul, ← sourceColumn_physical, kernelPullback_noise]

theorem noise_recover (u : ScalarSpace) : noiseLift (recover u) = physicalProjection u := rfl

attribute [local irreducible] contraction directional noiseLift recover physicalProjection

theorem averageGradient_physical (h : CoefficientSpace) (n : ℕ)
    {T : ℝ} (hT : 0 ≤ T) :
    physicalProjection (directional h (averageGradient n T)) =
      directional h (averageGradient n T) := by
  rw [averageGradient, ← (directional h).integral_comp_comm
    (clockGradient_integrable n hT)]
  rw [← physicalProjection.integral_comp_comm
    ((directional h).integrable_comp (clockGradient_integrable n hT))]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only
    rw [directional_clockGradient, map_smul, signedSource_physical]

theorem averageDomain (T : ℝ≥0) :
    flip (IBMTimeAveragedObservable.sourceAverage T) ∈ clockDerivative.domain :=
  (source_average_clock_domain T.property).choose

def gradient (T : ℝ≥0) : VectorSpace :=
  clockDerivative ⟨_, averageDomain T⟩

theorem gradient_graph (T : ℝ≥0) :
    (flip (IBMTimeAveragedObservable.sourceAverage T), gradient T) ∈
      clockDerivative.graph := by
  exact clockDerivative.mem_graph ⟨_, averageDomain T⟩

attribute [local irreducible] gradient averageGradient

theorem gradient_pairing_tendsto (T : ℝ≥0) (w : VectorSpace) :
    Tendsto (fun n => inner ℝ (averageGradient n T) w) atTop
      (𝓝 (inner ℝ (gradient T) w)) := by
  let E := 8 * IBMFoldedTransitionBound.peak 1 * (T : ℝ) ^ 2 * Real.sqrt T
  have hE : 0 ≤ E := (sq_nonneg ‖averageGradient 0 T‖).trans
    (averageGradient_uniform_energy 0 T.property)
  apply ClosedOperatorWeakGraphLimit.pairing_tendsto clockDerivative
    (BochnerClosedOperator.lift_isClosed gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_isClosed)
    (BochnerClosedOperator.lift_dense_domain gaussianProduct closedCylindricalDerivative
      closedCylindricalDerivative_dense_domain)
    (fun n => mollified_average_clock_graph n T.property) (gradient_graph T)
    (flip.continuous.continuousAt.tendsto.comp
      (IBMTimeAveragedObservable.average_tendsto T.property))
    (Real.sqrt E) (Real.sqrt_nonneg _) _ w
  intro n
  have hb := averageGradient_uniform_energy n T.property
  change ‖averageGradient n T‖ ^ 2 ≤ E at hb
  exact Real.le_sqrt_of_sq_le hb

theorem mapped_pairing_tendsto {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : VectorSpace →L[ℝ] F) (T : ℝ≥0) (w : F) :
    Tendsto (fun n => inner ℝ (L (averageGradient n T)) w) atTop
      (𝓝 (inner ℝ (L (gradient T)) w)) := by
  simpa only [← L.adjoint_inner_right] using gradient_pairing_tendsto T (L.adjoint w)

private theorem fixed_map_of_pairings {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (v : ℕ → E) (g : E) (L : E →L[ℝ] F) (P : F →L[ℝ] F)
    (hp : ∀ w, Tendsto (fun n => inner ℝ (v n) w) atTop (𝓝 (inner ℝ g w)))
    (hf : ∀ n, P (L (v n)) = L (v n)) : P (L g) = L g := by
  apply ext_inner_right ℝ
  intro w
  have hl := hp ((P.comp L).adjoint w)
  have hr := hp (L.adjoint w)
  simp only [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.comp_apply] at hl hr
  simp only [hf] at hl
  exact tendsto_nhds_unique hl hr

/-- Exact physical first-source-chaos recovery of the directional clock
 derivative. The passage to the limit uses weak pairings, not strong gradients. -/
theorem gradient_physical (h : CoefficientSpace) (T : ℝ≥0) :
    physicalProjection (directional h (gradient T)) = directional h (gradient T) :=
  fixed_map_of_pairings (fun n => averageGradient n T) (gradient T)
    (directional h) physicalProjection (gradient_pairing_tendsto T)
    (fun n => averageGradient_physical h n T.property)

def kernel (h : CoefficientSpace) (T : ℝ≥0) : Lp TimeHilbert 2 gaussianProduct :=
  recover (directional h (gradient T))

def kernelApprox (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    Lp TimeHilbert 2 gaussianProduct := recover (directional h (averageGradient n T))

theorem kernel_realization (h : CoefficientSpace) (T : ℝ≥0) :
    noiseLift (kernel h T) = directional h (gradient T) := by
  rw [kernel, noise_recover]
  exact gradient_physical h T

theorem kernel_unique (h : CoefficientSpace) (T : ℝ≥0)
    (u : Lp TimeHilbert 2 gaussianProduct)
    (hu : noiseLift u = directional h (gradient T)) : u = kernel h T := by
  apply noiseLift.injective
  exact hu.trans (kernel_realization h T).symm

theorem kernel_norm (h : CoefficientSpace) (T : ℝ≥0) :
    ‖kernel h T‖ = ‖directional h (gradient T)‖ := by
  rw [← kernel_realization, noiseLift.norm_map]

theorem kernel_pairing_tendsto (h : CoefficientSpace) (T : ℝ≥0)
    (w : Lp TimeHilbert 2 gaussianProduct) :
    Tendsto (fun n => inner ℝ (kernelApprox h n T) w) atTop
      (𝓝 (inner ℝ (kernel h T) w)) :=
  mapped_pairing_tendsto (recover.comp (directional h)) T w

/-- Genuine random-kernel white-noise equality for almost every clock sample.
Each inner equality is an L2(source) equality, not a pathwise white-noise value. -/
theorem kernel_realization_ae (h : CoefficientSpace) (T : ℝ≥0) :
    ∀ᵐ Y ∂gaussianProduct,
      physicalNoise (kernel h T Y) = directional h (gradient T) Y := by
  have he : noiseLift (kernel h T) =ᵐ[gaussianProduct]
      fun Y => physicalNoise (kernel h T Y) := by
    simpa only [noiseLift] using
      BochnerLinearIsometry.lift_coeFn gaussianProduct physicalNoise (kernel h T)
  rw [kernel_realization] at he
  exact he.symm

theorem recovered_signedSource_ae (n : ℕ) (t : ℝ≥0) :
    recover (signedSource n t) =ᵐ[gaussianProduct] fun Y =>
      BrownianSignIntegral.signum (IBMConstructedSources.clockPath Y t) •
        IBMPhysicalDerivativeKernel.translatedClass (IBMMollifier.kernel n)
          (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n)
          |IBMConstructedSources.clockPath Y t| := by
  have ha : recover (signedSource n t) =ᵐ[gaussianProduct]
      fun Y => kernelPullback (signedSource n t Y) := by
    simpa only [recover] using kernelPullback.coeFn_compLpL (signedSource n t)
  filter_upwards [ha, signedSource_ae n t] with Y hr hs
  rw [hr, hs]
  change kernelPullback (_ • IBMClockAverageCandidate.sourceColumn n _) = _
  rw [map_smul, ← sourceColumn_physical, kernelPullback_noise,
    IBMPhysicalDerivativeKernel.derivative_eq_translated
      ((IBMMollifier.kernel_smooth n).of_le (by simp))
      (IBMMollifier.kernel_compactSupport n)]

theorem kernelApprox_integrable (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    Integrable (fun t : ℝ => inner ℝ h (IBMClockAverageCandidate.direction t.toNNReal) •
      recover (signedSource n t.toNNReal)) (IBMClockOverlapEnergy.window T) := by
  have hi := (recover.comp (directional h)).integrable_comp
    (clockGradient_integrable n T.property)
  apply hi.congr
  exact ae_of_all _ fun t => by
    dsimp only [ContinuousLinearMap.comp_apply, Function.comp_def]
    rw [directional_clockGradient, map_smul]

/-- Exact Bochner L2(clock;L2(space)) formula for the finite-width weighted
occupation kernels. The preceding a.e. theorem identifies every time slice
as sign(B_t) rho_n(abs(B_t)-space). -/
theorem kernelApprox_integral (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    kernelApprox h n T =
      ∫ t : ℝ, inner ℝ h (IBMClockAverageCandidate.direction t.toNNReal) •
        recover (signedSource n t.toNNReal) ∂IBMClockOverlapEnergy.window T := by
  let f : ℝ → VectorSpace := fun t => clockGradient n t.toNNReal
  have hi : Integrable f (IBMClockOverlapEnergy.window T) :=
    clockGradient_integrable n T.property
  rw [kernelApprox, averageGradient]
  change recover (directional h (∫ t, f t ∂IBMClockOverlapEnergy.window T)) = _
  calc
    _ = recover (∫ t, directional h (f t) ∂IBMClockOverlapEnergy.window T) :=
      congrArg recover ((directional h).integral_comp_comm hi).symm
    _ = ∫ t, recover (directional h (f t)) ∂IBMClockOverlapEnergy.window T :=
      (recover.integral_comp_comm ((directional h).integrable_comp hi)).symm
    _ = _ := integral_congr_ae (ae_of_all _ fun t => by
      dsimp only [f]
      rw [directional_clockGradient, map_smul])

theorem kernelApprox_realization (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    noiseLift (kernelApprox h n T) = directional h (averageGradient n T) := by
  rw [kernelApprox, noise_recover]
  exact averageGradient_physical h n T.property

/-- The norm identity is exact at every width; it does not assert convergence
of norms, which would require a strong-convergence argument. -/
theorem kernelApprox_norm (h : CoefficientSpace) (n : ℕ) (T : ℝ≥0) :
    ‖kernelApprox h n T‖ = ‖directional h (averageGradient n T)‖ := by
  rw [← kernelApprox_realization, noiseLift.norm_map]

theorem kernel_test_pairing (h : CoefficientSpace) (T : ℝ≥0)
    (w : Lp TimeHilbert 2 gaussianProduct) :
    inner ℝ (kernel h T) w =
      inner ℝ (directional h (gradient T)) (noiseLift w) := by
  rw [← kernel_realization, noiseLift.inner_map_map]

end OperatorDerivativeRewrite.Foundation.IBMClockPhysicalOccupation
