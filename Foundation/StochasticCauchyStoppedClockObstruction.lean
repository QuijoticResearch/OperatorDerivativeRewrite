import Foundation.StochasticCauchyBoundaryConstraint
import Foundation.GaussianTimeHilbert
import Foundation.GaussianHilbertProcess
import Foundation.GaussianFirstChaosRecovery
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Probability.BrownianMotion.Basic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedClockObstruction
open InfiniteGaussian GaussianTimeHilbert SeparableHilbertEmbedding

local instance : SecondCountableTopology TimeHilbert := timeHilbert_secondCountable

abbrev TimePair := WithLp 2 (TimeHilbert × TimeHilbert)

def axis (second : Bool) (t : ℝ≥0) : TimePair :=
  if second then WithLp.toLp 2 (0, timeVector t)
  else WithLp.toLp 2 (timeVector t, 0)

def direction (second : Bool) (t : ℝ≥0) : CoefficientSpace :=
  hilbertEmbedding TimePair (axis second t)

theorem direction_norm_sq (second : Bool) (t : ℝ≥0) :
    ‖direction second t‖ ^ 2 = (t : ℝ) := by
  rw [direction, (hilbertEmbedding TimePair).norm_map]
  cases second <;> simp [axis, timeVector_norm_sq]

theorem direction_cross (s t : ℝ≥0) :
    inner ℝ (direction false s) (direction true t) = 0 := by
  rw [direction, direction, (hilbertEmbedding TimePair).inner_map_map]
  simp [axis, WithLp.prod_inner_apply]

theorem direction_inner (second : Bool) (s t : ℝ≥0) :
    inner ℝ (direction second s) (direction second t) = min (s : ℝ) (t : ℝ) := by
  rw [direction, direction, (hilbertEmbedding TimePair).inner_map_map]
  cases second <;> simp [axis, WithLp.prod_inner_apply, timeVector_inner]

theorem direction_zero (second : Bool) : direction second 0 = 0 := by
  apply norm_eq_zero.mp
  exact sq_eq_zero_iff.mp (by simpa using direction_norm_sq second 0)

/-- Actual jointly Gaussian coordinates on the existing Gaussian product. No
continuous modification or random-time domain is inferred from this definition. -/
def process (second : Bool) (t : ℝ≥0) : SampleSpace → ℝ :=
  firstChaosEmbedding (direction second t)

/-- The proposed time kernels really are the original derivatives at fixed
times. The obstruction is their unsupported substitution at an exit clock. -/
theorem fixed_time_graph (second : Bool) (t : ℝ≥0) :
    (firstChaosEmbedding (direction second t),
      scalarTensor (direction second t) gaussianOne) ∈ closedCylindricalDerivative.graph :=
  GaussianFirstChaosRecovery.firstChaos_derivative_graph _

theorem process_jointGaussian :
    IsGaussianProcess (fun i : Bool × ℝ≥0 => process i.1 i.2) gaussianProduct :=
  firstChaos_isGaussianProcess.comp_right (fun i : Bool × ℝ≥0 => direction i.1 i.2)

theorem process_covariance (second : Bool) (s t : ℝ≥0) :
    cov[process second s, process second t; gaussianProduct] =
      min (s : ℝ) (t : ℝ) :=
  (firstChaos_covariance _ _).trans (direction_inner second s t)

theorem process_cross_covariance (s t : ℝ≥0) :
    cov[process false s, process true t; gaussianProduct] = 0 :=
  (firstChaos_covariance _ _).trans (direction_cross s t)

/-- Brownian finite-dimensional laws, not a continuous modification. -/
theorem process_isPreBrownian (second : Bool) :
    IsPreBrownianReal (process second) gaussianProduct := by
  have hG : IsGaussianProcess (process second) gaussianProduct :=
    firstChaos_isGaussianProcess.comp_right (direction second)
  apply hG.isPreBrownianReal_of_covariance
  · intro t
    exact firstChaos_integral _
  · intro s t hst
    rw [process_covariance]
    exact min_eq_left (show (s : ℝ) ≤ (t : ℝ) from hst)

theorem process_origin (second : Bool) :
    process second 0 =ᵐ[gaussianProduct] fun _ => 0 := by
  unfold process
  rw [direction_zero, map_zero]
  exact Lp.coeFn_zero _ _ _

/-- The flat random-time kernel asserted in the manuscript forces the clock
to vanish under the ORIGINAL full derivative graphs and circle boundary law.
No stopping-time measurability or domain assumption is manufactured. -/
theorem flat_circle_clock_zero (τ : SampleSpace → ℝ≥0)
    (f h : GaussianL2) (g k : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (hhk : (h, k) ∈ closedCylindricalDerivative.graph)
    (hc : ∀ᵐ w ∂gaussianProduct, (f w) ^ 2 + (h w) ^ 2 = 1)
    (hg : g =ᵐ[gaussianProduct] fun w => direction false (τ w))
    (hk : k =ᵐ[gaussianProduct] fun w => direction true (τ w)) :
    τ =ᵐ[gaussianProduct] fun _ => 0 := by
  have ho : ∀ᵐ w ∂gaussianProduct, inner ℝ (g w) (k w) = 0 := by
    filter_upwards [hg, hk] with w hg hk
    rw [hg, hk]; exact direction_cross _ _
  have hn : ∀ᵐ w ∂gaussianProduct, ‖g w‖ = ‖k w‖ := by
    filter_upwards [hg, hk] with w hg hk
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [hg, hk, direction_norm_sq, direction_norm_sq]
  obtain ⟨hzero, _⟩ := StochasticCauchyBoundaryConstraint.circle_isotropic_zero
    f h g k hfg hhk hc ho hn
  have he : g =ᵐ[gaussianProduct] fun _ => 0 := by
    rw [hzero]; exact Lp.coeFn_zero _ _ _
  filter_upwards [hg, he] with w hg he
  apply NNReal.coe_injective
  have hh := direction_norm_sq false (τ w)
  rw [← hg, he, norm_zero] at hh
  simpa using hh.symm

/-- A boundary-supported stopped value of these actual Gaussian coordinates
cannot have the proposed flat full gradients. This is a no-go theorem for the
template, not a construction of an exit time or its law. -/
theorem stopped_circle_flat_impossible (τ : SampleSpace → ℝ≥0)
    (f h : GaussianL2) (g k : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (hhk : (h, k) ∈ closedCylindricalDerivative.graph)
    (hc : ∀ᵐ w ∂gaussianProduct, (f w) ^ 2 + (h w) ^ 2 = 1)
    (hg : g =ᵐ[gaussianProduct] fun w => direction false (τ w))
    (hk : k =ᵐ[gaussianProduct] fun w => direction true (τ w))
    (hf : f =ᵐ[gaussianProduct] fun w => process false (τ w) w)
    (hh : h =ᵐ[gaussianProduct] fun w => process true (τ w) w) : False := by
  have ht := flat_circle_clock_zero τ f h g k hfg hhk hc hg hk
  have bad : ∀ᵐ w ∂gaussianProduct, False := by
    filter_upwards [ht, hf, hh, hc, process_origin false, process_origin true]
      with w ht hf hh hc hx hy
    rw [ht, hx] at hf
    rw [ht, hy] at hh
    rw [hf, hh] at hc
    norm_num at hc
  obtain ⟨w, hw⟩ := bad.exists
  exact hw

end OperatorDerivativeRewrite.Foundation.StochasticCauchyStoppedClockObstruction
