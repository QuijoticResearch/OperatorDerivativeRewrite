import Foundation.IBMDilatedMollifier
import Foundation.IBMSchwartzFullGlobalBounds

/-! Full, unprojected nonlinear scenery curves for arbitrary compact kernels.
The derivatives and bounds are obtained from the existing source calculus. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.IBMCompactKernelSchwartz
open InfiniteGaussian IBMContinuousScenery IBMCorrectionStein
open IBMSchwartzSourceDerivative IBMSchwartzSourceSecondDerivative
open IBMSchwartzSecondProjection IBMSchwartzSourceContinuity
open IBMSchwartzHeatBounds
set_option backward.isDefEq.respectTransparency false

def coefficient (ρ : ℝ → ℝ) (r : ℝ) : CoefficientSpace :=
  firstChaosEmbedding.toContinuousLinearMap.adjoint (wholeLineScenery ρ r)

theorem coefficient_embedding (ρ : ℝ → ℝ) (r : ℝ) :
    firstChaosEmbedding (coefficient ρ r) = wholeLineScenery ρ r := by
  rw [coefficient,IBMJointMollifierGaussian.wholeLineScenery_eq_sourceEmbedding]
  change firstChaosEmbedding
    (firstChaosEmbedding.toContinuousLinearMap.adjoint (firstChaosEmbedding _)) = _
  rw [IBMQuarticSecondPrimitive.adjoint_embedding]
  rfl

theorem coefficient_hasDerivAt {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (r : ℝ) :
    HasDerivAt (coefficient ρ) (coefficient (deriv ρ) r) r :=
  firstChaosEmbedding.toContinuousLinearMap.adjoint.hasFDerivAt.comp_hasDerivAt r
    (wholeLineScenery_hasDerivAt hc hρ r)

theorem coefficient_continuous {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) : Continuous (coefficient ρ) :=
  continuous_iff_continuousAt.mpr fun r => (coefficient_hasDerivAt hc hρ r).continuousAt

def spatial (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : GaussianL2 :=
  observable g a 0 (coefficient ρ r)

def slope (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : GaussianL2 :=
  weightedClass g a (coefficient ρ r) 1 (firstChaosEmbedding (coefficient (deriv ρ) r))

def curvature (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (r : ℝ) : GaussianL2 :=
  correctionClass g a (coefficient ρ r) (coefficient (deriv ρ) r)
    (coefficient (deriv (deriv ρ)) r)

/-- Representative is the actual nonlinear observable of the Bochner convolution. -/
theorem spatial_ae (g : SchwartzMap ℝ ℝ) (a : ℝ) (ρ : ℝ → ℝ) (r : ℝ) :
    spatial g a ρ r =ᵐ[gaussianProduct] fun ω => shiftedJet g a 0 (wholeLineScenery ρ r ω) := by
  simpa only [spatial,coefficient_embedding] using observable_coeFn g a 0 (coefficient ρ r)

theorem spatial_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 1 ρ) (r : ℝ) :
    HasDerivAt (spatial g a ρ) (slope g a ρ r) r :=
  observable_comp_hasDerivAt g a 0 (coefficient_hasDerivAt hc hρ r)

theorem slope_hasDerivAt (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) (r : ℝ) :
    HasDerivAt (slope g a ρ) (curvature g a ρ r) r := by
  change HasDerivAt (fun x => weightedClass g a (coefficient ρ x) 1
    (firstChaosEmbedding (coefficient (deriv ρ) x))) _ r
  simpa only [curvature,correctionClass,Nat.zero_add,rawProduct_self] using
    weighted_linear_hasDerivAt g a 0 (coefficient_hasDerivAt hc (hρ.of_le (by norm_num)) r)
      (coefficient_hasDerivAt hc.deriv (hρ.deriv' (n := 1)) r)

theorem curvature_continuous (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) : Continuous (curvature g a ρ) := by
  have h0 := coefficient_continuous hc (hρ.of_le (by norm_num))
  have h1 := coefficient_continuous hc.deriv ((hρ.deriv' (n := 2)).of_le (by norm_num))
  have h2 := coefficient_continuous hc.deriv.deriv ((hρ.deriv' (n := 2)).deriv' (n := 1))
  exact (weighted_square_continuous_of g a 2 h0 h1).add
    (weighted_linear_continuous_of g a 1 h0 h2)

theorem spatial_C2 (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 3 ρ) : ContDiff ℝ 2 (spatial g a ρ) := by
  have he : deriv (spatial g a ρ) = slope g a ρ :=
    funext fun r => (spatial_hasDerivAt g a hc (hρ.of_le (by norm_num)) r).deriv
  have hd : deriv (slope g a ρ) = curvature g a ρ :=
    funext fun r => (slope_hasDerivAt g a hc (hρ.of_le (by norm_num)) r).deriv
  have hs : ContDiff ℝ 1 (slope g a ρ) := contDiff_one_iff_deriv.mpr
    ⟨fun r => (slope_hasDerivAt g a hc (hρ.of_le (by norm_num)) r).differentiableAt,
      by rw [hd]; exact curvature_continuous g a hc hρ⟩
  rw [show (2 : WithTop ℕ∞) = 1+1 by norm_num,contDiff_succ_iff_deriv]
  exact ⟨fun r => (spatial_hasDerivAt g a hc (hρ.of_le (by norm_num)) r).differentiableAt,
    by simp,by rw [he];exact hs⟩

theorem derivative_coefficient_norm {ρ : ℝ → ℝ} (hc : HasCompactSupport ρ)
    (hρ : ContDiff ℝ 1 ρ) (r : ℝ) :
    ‖coefficient (deriv ρ) r‖ = (eLpNorm ρ 2 volume).toReal := by
  rw [coefficient,← IBMPhysicalNoiseCalculus.convolutionKernel_coefficient
    (hρ.continuous_deriv le_rfl) hc.deriv r,
    IBMPhysicalNoiseRealization.physicalToCoefficient.norm_map,
    IBMPhysicalDerivativeKernel.derivative_eq_translated hρ hc]
  exact IBMSchwartzPhysicalGlobalBounds.translated_norm _ _ _ _

/-- Bounds are uniform over the whole real spatial line, at each fixed kernel. -/
theorem slope_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖slope g a ρ r‖ ≤ C := by
  refine ⟨SchwartzMap.seminorm ℝ 0 0 (jet g 1) *
    (eLpNorm ρ 2 volume).toReal,by positivity,fun r => ?_⟩
  have he := weightedClass_norm_le g a (coefficient ρ r) 1
    (firstChaosEmbedding (coefficient (deriv ρ) r))
  rw [firstChaosEmbedding.norm_map,derivative_coefficient_norm hc (hρ.of_le (by norm_num))] at he
  exact he

theorem curvature_bound (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : ContDiff ℝ 2 ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r, ‖curvature g a ρ r‖ ≤ C := by
  refine ⟨2*SchwartzMap.seminorm ℝ 0 0 (jet g 2)*
    (eLpNorm ρ 2 volume).toReal^2+
    SchwartzMap.seminorm ℝ 0 0 (jet g 1)*
      (eLpNorm (deriv ρ) 2 volume).toReal,by positivity,fun r => ?_⟩
  have he := correction_norm_le g a (coefficient ρ r) (coefficient (deriv ρ) r)
    (coefficient (deriv (deriv ρ)) r)
  rw [derivative_coefficient_norm hc (hρ.of_le (by norm_num)),
    derivative_coefficient_norm hc.deriv (hρ.deriv' (n := 1))] at he
  exact he

/-- Strong nonlinear convergence for every positive-width family and every profile. -/
theorem spatial_tendsto {ι : Type*} {l : Filter ι} {ε : ι → ℝ}
    (hε : ∀ i, 0 < ε i) (hlim : Tendsto ε l (𝓝 0))
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hc : HasCompactSupport ρ)
    (hpos : ∀ z, 0 ≤ ρ z) (hmass : (∫ z, ρ z) = 1)
    (g : SchwartzMap ℝ ℝ) (a x : ℝ) :
    Tendsto (fun i => spatial g a (IBMDilatedMollifier.dilate ρ (ε i)) x) l
      (𝓝 (observable g a 0 (IBMQuarticPrimitiveLimit.baseCoefficient x))) := by
  have hs := IBMDilatedMollifier.scenery_tendsto hε hlim hρ hc hpos hmass x
  exact ((observable_continuous g a 0).tendsto _).comp
    (firstChaosEmbedding.toContinuousLinearMap.adjoint.continuous.tendsto _ |>.comp hs)

end OperatorDerivativeRewrite.Foundation.IBMCompactKernelSchwartz
