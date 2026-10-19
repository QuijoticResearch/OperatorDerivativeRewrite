import Foundation.IBMSchwartzPhysicalFirstKernel

/-! The actual physical first-source primitive and its two spatial derivatives.
The curvature and origin are derivatives of one primitive, before taking any
singular limit or claiming a target-valued stochastic chain rule. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal
namespace OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalPrimitive
open InfiniteGaussian GaussianTimeHilbert IBMCorrectionStein IBMShiftedJetMoments
open IBMSchwartzFirstCoefficient IBMSchwartzSourceDerivative IBMFirstChaosMixedStein
open IBMPhysicalNoiseClock IBMPhysicalNoiseCalculus IBMPhysicalNoiseRealization
open IBMSchwartzPhysicalFirstKernel IBMGaussianSteinMoments

theorem observable_adjoint (g : SchwartzMap ℝ ℝ) (a : ℝ) (j : ℕ) (u : CoefficientSpace) :
    firstChaosEmbedding.toContinuousLinearMap.adjoint (observable g a j u) =
      M g a u (j+1) 0 • u := by
  apply ext_inner_right ℝ
  intro k
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (observable g a j u) (firstChaosEmbedding k) = _
  rw [real_inner_comm]
  change inner ℝ (firstChaosEmbedding k)
    (testClass u (shiftedJet_smooth g a j).continuous (shiftedJet_bound g a j)) = _
  rw [first_pairing_integral]
  have hb : ∀ x, ‖deriv (shiftedJet g a j) x‖ ≤
      SchwartzMap.seminorm ℝ 0 0 (jet g (j+1)) := by
    rw [shiftedJet_deriv]
    exact shiftedJet_bound g a (j+1)
  rw [first_mixed ((shiftedJet_smooth g a j).of_le (by norm_num))
    (shiftedJet_bound g a j) hb, shiftedJet_deriv, ← moment_zero]
  simp only [real_inner_smul_left]
  ring

def primitive (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : TimeHilbert :=
  kernelPullback (IBMFullSchwartzTerminal.spatial g a n r)

def slope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) : TimeHilbert :=
  kernelPullback (IBMSchwartzSourceSecondDerivative.spatialSlope g a n r)

theorem primitive_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    primitive g a n r = M g a (tripleCoefficient n r 0) 1 0 • physicalJet n r 0 := by
  change physicalToCoefficient.toContinuousLinearMap.adjoint
    (firstChaosEmbedding.toContinuousLinearMap.adjoint (observable g a 0 (tripleCoefficient n r 0))) = _
  rw [observable_adjoint, map_smul, ← triple_coefficient_physical, physical_adjoint_leftInverse]

theorem primitive_embeds (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    physicalToCoefficient (primitive g a n r) =
      firstChaosEmbedding.toContinuousLinearMap.adjoint (IBMFullSchwartzTerminal.spatial g a n r) := by
  rw [primitive_eq, map_smul, physicalJet, triple_coefficient_physical]
  exact (observable_adjoint g a 0 (tripleCoefficient n r 0)).symm

theorem primitive_realizes_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    physicalNoise (primitive g a n r) =
      GaussianPastFirstChaos.projection (IBMFullSchwartzTerminal.spatial g a n r) := by
  change firstChaosEmbedding (physicalToCoefficient (primitive g a n r)) =
    firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint _)
  rw [primitive_embeds]

theorem slope_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    slope g a n r =
      (inner ℝ (tripleCoefficient n r 0) (tripleCoefficient n r 1)*
        M g a (tripleCoefficient n r 0) 3 0) • physicalJet n r 0+
      M g a (tripleCoefficient n r 0) 1 0 • physicalJet n r 1 := by
  change physicalToCoefficient.toContinuousLinearMap.adjoint
    (firstChaosEmbedding.toContinuousLinearMap.adjoint
      (IBMSchwartzSecondProjection.weightedClass g a (tripleCoefficient n r 0) 1
        (firstChaosEmbedding (tripleCoefficient n r 1)))) = _
  rw [weighted_linear_adjoint, map_add, map_smul, map_smul,
    ← triple_coefficient_physical, ← triple_coefficient_physical,
    physical_adjoint_leftInverse, physical_adjoint_leftInverse]
  exact add_comm _ _

theorem primitive_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (primitive g a n) (slope g a n r) r :=
  kernelPullback.hasFDerivAt.comp_hasDerivAt r
    (IBMSchwartzSourceSecondDerivative.spatial_hasDerivAt g a n r)

theorem slope_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (slope g a n) (curvatureKernel g a n r) r := by
  have he := kernelPullback.hasFDerivAt.comp_hasDerivAt r
    (IBMSchwartzSourceSecondDerivative.spatialSlope_hasDerivAt g a n r)
  change HasDerivAt (slope g a n)
    (kernelPullback (IBMSchwartzSecondProjection.mollifiedClass g a n r)) r at he
  rw [curvatureKernel_eq_pullback] at he
  exact he

theorem primitive_second_deriv (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (r : ℝ) :
    deriv (deriv (primitive g a n)) r = curvatureKernel g a n r := by
  have he : deriv (primitive g a n) = slope g a n :=
    funext fun x => (primitive_hasDerivAt g a n x).deriv
  rw [he]
  exact (slope_hasDerivAt g a n r).deriv

theorem slope_origin (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    slope g a n 0 = originKernel g a n := by
  rw [slope_eq, IBMSchwartzWholeSourceMean.origin_covariance_zero, zero_mul, zero_smul, zero_add]
  rfl

theorem primitive_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (primitive g a n) :=
  continuous_iff_continuousAt.mpr fun r => (primitive_hasDerivAt g a n r).continuousAt

theorem slope_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    Continuous (slope g a n) :=
  continuous_iff_continuousAt.mpr fun r => (slope_hasDerivAt g a n r).continuousAt

theorem primitive_C2 (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) :
    ContDiff ℝ 2 (primitive g a n) := by
  have he : deriv (primitive g a n) = slope g a n :=
    funext fun r => (primitive_hasDerivAt g a n r).deriv
  have hd : deriv (slope g a n) = curvatureKernel g a n :=
    funext fun r => (slope_hasDerivAt g a n r).deriv
  have hs : ContDiff ℝ 1 (slope g a n) := contDiff_one_iff_deriv.mpr
    ⟨fun r => (slope_hasDerivAt g a n r).differentiableAt,
      by rw [hd]; exact curvatureKernel_continuous g a n⟩
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num, contDiff_succ_iff_deriv]
  exact ⟨fun r => (primitive_hasDerivAt g a n r).differentiableAt,
    by simp, by rw [he]; exact hs⟩

/-- The boundary coefficient is the right spatial slope of the same
primitive as the bulk curvature. This is not a stochastic chain rule. -/
theorem wholeKernel_derivatives (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ)
    (T : ℝ≥0) (ω : SampleSpace) :
    wholeKernel g a n T ω =
      BrownianMassLimitIdentification.coordinateClass T ω • deriv (primitive g a n) 0+
        (1/2 : ℝ) • ∫ s in 0..(T : ℝ), deriv (deriv (primitive g a n))
          |IBMConstructedSources.clockPath ω s.toNNReal| := by
  simp only [primitive_second_deriv, (primitive_hasDerivAt g a n 0).deriv, slope_origin]
  rfl

theorem integral_curvature (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (b c : ℝ) :
    (∫ r in b..c, curvatureKernel g a n r) = slope g a n c-slope g a n b :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => slope_hasDerivAt g a n r)
    ((curvatureKernel_continuous g a n).intervalIntegrable b c)

theorem integral_slope (g : SchwartzMap ℝ ℝ) (a : ℝ) (n : ℕ) (b c : ℝ) :
    (∫ r in b..c, slope g a n r) = primitive g a n c-primitive g a n b :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => primitive_hasDerivAt g a n r)
    ((slope_continuous g a n).intervalIntegrable b c)

def primitiveLimit (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) : TimeHilbert :=
  kernelPullback (IBMFullSchwartzTerminal.spatialLimit g a r)

theorem primitiveLimit_eq (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    primitiveLimit g a r = M g a (IBMQuarticPrimitiveLimit.baseCoefficient r) 1 0 •
      IBMPhysicalNoiseVectors.vector r := by
  change physicalToCoefficient.toContinuousLinearMap.adjoint
    (firstChaosEmbedding.toContinuousLinearMap.adjoint
      (observable g a 0 (IBMQuarticPrimitiveLimit.baseCoefficient r))) = _
  rw [observable_adjoint, map_smul, ← physicalToCoefficient_vector, physical_adjoint_leftInverse]

theorem primitiveLimit_realizes_projection (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    physicalNoise (primitiveLimit g a r) =
      GaussianPastFirstChaos.projection (IBMFullSchwartzTerminal.spatialLimit g a r) := by
  change firstChaosEmbedding (physicalToCoefficient (primitiveLimit g a r)) =
    firstChaosEmbedding (firstChaosEmbedding.toContinuousLinearMap.adjoint _)
  rw [primitiveLimit_eq, map_smul, physicalToCoefficient_vector]
  exact congrArg firstChaosEmbedding (observable_adjoint g a 0 _).symm

theorem primitiveLimit_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) :
    Continuous (primitiveLimit g a) :=
  kernelPullback.continuous.comp (IBMFullSchwartzTerminal.spatialLimit_continuous g a)

theorem primitive_tendsto (g : SchwartzMap ℝ ℝ) (a : ℝ) (r : ℝ) :
    Tendsto (fun n => primitive g a n r) atTop (𝓝 (primitiveLimit g a r)) :=
  kernelPullback.continuous.tendsto _ |>.comp (IBMFullSchwartzTerminal.spatial_tendsto g a r)

end OperatorDerivativeRewrite.Foundation.IBMSchwartzPhysicalPrimitive
