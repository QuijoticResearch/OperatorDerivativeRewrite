import Foundation.GaussianClosedChainRule
import Foundation.GaussianSobolevCutoffs

/-! Boundary constraints for the actual closed Gaussian derivative.  These
results impose Sobolev domain hypotheses; they do not construct an exit time. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyBoundaryConstraint
open InfiniteGaussian

private def squareBump : ContDiffBump (0 : ℝ) := ⟨2, 3, by norm_num, by norm_num⟩
private def boundedSquare (x : ℝ) : ℝ := squareBump x * x ^ 2

private theorem square_smooth : ContDiff ℝ ∞ boundedSquare :=
  squareBump.contDiff.mul (contDiff_id.pow 2)

private theorem square_local (x : ℝ) (hx : |x| ≤ 1) :
    boundedSquare =ᶠ[𝓝 x] (fun y => y ^ 2) := by
  have hx2 : x ∈ Metric.ball (0 : ℝ) 2 := by
    simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    linarith
  filter_upwards [Metric.isOpen_ball.mem_nhds hx2] with y hy
  have hb : squareBump y = 1 := squareBump.one_of_mem_closedBall (by
    exact Metric.closedBall_subset_closedBall (by norm_num : (2 : ℝ) ≤ 2)
      (Metric.ball_subset_closedBall hy))
  simp [boundedSquare, hb]

private theorem square_value (x : ℝ) (hx : |x| ≤ 1) : boundedSquare x = x ^ 2 :=
  (square_local x hx).eq_of_nhds

private theorem square_deriv (x : ℝ) (hx : |x| ≤ 1) : deriv boundedSquare x = 2 * x := by
  rw [(square_local x hx).deriv_eq]
  simp

private theorem square_bounds : ∃ A B : ℝ,
    (∀ x, ‖boundedSquare x‖ ≤ A) ∧ (∀ x, ‖deriv boundedSquare x‖ ≤ B) := by
  have hs : HasCompactSupport boundedSquare := squareBump.hasCompactSupport.mul_right
  obtain ⟨A, hA⟩ := square_smooth.continuous.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hd : Continuous (deriv boundedSquare) := square_smooth.continuous_deriv (by norm_num)
  obtain ⟨B, hB⟩ := hd.norm.bddAbove_range_of_hasCompactSupport hs.deriv.norm
  exact ⟨A, B, fun x => hA (mem_range_self x), fun x => hB (mem_range_self x)⟩

/-- Squaring on a bounded observable uses the existing full closed-domain chain
rule, not an assumed Leibniz rule on an unspecified domain. -/
theorem bounded_square_graph (f : GaussianL2) (g : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (hf : ∀ᵐ w ∂gaussianProduct, |f w| ≤ 1) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun w => (f w) ^ 2) ∧
      G =ᵐ[gaussianProduct] (fun w => (2 * f w) • g w) := by
  obtain ⟨A, B, hA, hB⟩ := square_bounds
  obtain ⟨F, G, hgraph, hF, hG⟩ := GaussianClosedChainRule.bounded_closed_chain_graph f g hfg
    boundedSquare (deriv boundedSquare)
    (fun x => (square_smooth.differentiable (by norm_num) x).hasDerivAt)
    (square_smooth.continuous_deriv (by norm_num)) A B hA hB
  refine ⟨F, G, hgraph, ?_, ?_⟩
  · filter_upwards [hF, hf] with w hF hf
    exact hF.trans (square_value _ hf)
  · filter_upwards [hG, hf] with w hG hf
    simpa only [square_deriv _ hf] using hG

/-- The full Sobolev gradient of a circle-valued pair must be tangent. -/
theorem circle_tangency (f h : GaussianL2) (g k : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (hhk : (h, k) ∈ closedCylindricalDerivative.graph)
    (hcircle : ∀ᵐ w ∂gaussianProduct, (f w) ^ 2 + (h w) ^ 2 = 1) :
    ∀ᵐ w ∂gaussianProduct, f w • g w + h w • k w = 0 := by
  have hf : ∀ᵐ w ∂gaussianProduct, |f w| ≤ 1 := by
    filter_upwards [hcircle] with w hc
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (h w)]
  have hh : ∀ᵐ w ∂gaussianProduct, |h w| ≤ 1 := by
    filter_upwards [hcircle] with w hc
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (f w)]
  obtain ⟨F, G, hFG, hF, hG⟩ := bounded_square_graph f g hfg hf
  obtain ⟨H, K, hHK, hH, hK⟩ := bounded_square_graph h k hhk hh
  have hsum : F + H = gaussianOne := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add F H, hF, hH, gaussianOne_coeFn, hcircle] with w hs hf hh h1 hc
    simp only [Pi.add_apply] at hs
    rw [hs, hf, hh, h1]
    exact hc
  have hgk : G + K = 0 := by
    apply closedCylindricalDerivative.mem_graph_snd_inj
      (closedCylindricalDerivative.graph.add_mem hFG hHK)
      (closedDerivative_constant_graph 1)
    simpa using hsum
  have hae : ∀ᵐ w ∂gaussianProduct, G w + K w = 0 := by
    filter_upwards [Lp.coeFn_add G K, Lp.coeFn_zero (E := CoefficientSpace) (p := 2)
      (μ := gaussianProduct)] with w hs hz
    have he := congrArg (fun a : GaussianVectorL2 => a w) hgk
    simp only [Pi.add_apply] at hs
    rw [hs, hz] at he
    exact he
  filter_upwards [hae, hG, hK] with w he hg hk
  rw [hg, hk] at he
  have he' : (2 : ℝ) • (f w • g w + h w • k w) = 0 := by
    simpa only [smul_add, smul_smul] using he
  exact (smul_eq_zero.mp he').resolve_left (by norm_num)


/-- The permitted correction has one tangent channel, realized as an actual L2
random field.  Its energy is exactly the sum of both coordinate energies. -/
theorem circle_gradient_factorization (f h : GaussianL2) (g k : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (hhk : (h, k) ∈ closedCylindricalDerivative.graph)
    (hc : ∀ᵐ w ∂gaussianProduct, (f w) ^ 2 + (h w) ^ 2 = 1) :
    ∃ W : GaussianVectorL2,
      g =ᵐ[gaussianProduct] (fun w => h w • W w) ∧
      k =ᵐ[gaussianProduct] (fun w => (-f w) • W w) ∧
      (∀ᵐ w ∂gaussianProduct, ‖W w‖ ^ 2 = ‖g w‖ ^ 2 + ‖k w‖ ^ 2) := by
  have hf : ∀ᵐ w ∂gaussianProduct, ‖f w‖ ≤ 1 := by
    filter_upwards [hc] with w hw
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (h w)]
  have hh : ∀ᵐ w ∂gaussianProduct, ‖h w‖ ≤ 1 := by
    filter_upwards [hc] with w hw
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith [sq_nonneg (f w)]
  let U := GaussianClosedChainRule.multiplier h (Lp.aestronglyMeasurable h) 1 hh g
  let V := GaussianClosedChainRule.multiplier f (Lp.aestronglyMeasurable f) 1 hf k
  let W : GaussianVectorL2 := U - V
  have hW : W =ᵐ[gaussianProduct] fun w => h w • g w - f w • k w := by
    filter_upwards [Lp.coeFn_sub U V,
      GaussianClosedChainRule.multiplier_ae h (Lp.aestronglyMeasurable h) 1 hh g,
      GaussianClosedChainRule.multiplier_ae f (Lp.aestronglyMeasurable f) 1 hf k] with w hs hu hv
    have hu' : U w = h w • g w := hu
    have hv' : V w = f w • k w := hv
    exact hs.trans (by simp only [Pi.sub_apply, hu', hv'])
  have ht := circle_tangency f h g k hfg hhk hc
  have hfactor : ∀ᵐ w ∂gaussianProduct,
      g w = h w • W w ∧ k w = (-f w) • W w := by
    filter_upwards [hW, ht, hc] with w hw ht hc
    have he : h w • W w = ((f w)^2+(h w)^2) • g w -
        f w • (f w • g w+h w • k w) := by rw [hw]; module
    have he' : (-f w) • W w = ((f w)^2+(h w)^2) • k w -
        h w • (f w • g w+h w • k w) := by rw [hw]; module
    rw [hc, ht] at he he'
    exact ⟨by simpa using he.symm, by simpa using he'.symm⟩
  refine ⟨W, hfactor.mono (fun _ hw => hw.1), hfactor.mono (fun _ hw => hw.2), ?_⟩
  filter_upwards [hfactor, hc] with w hw hc
  rw [hw.1, hw.2, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    mul_pow, mul_pow, sq_abs, sq_abs, neg_sq, ← add_mul, add_comm ((h w)^2), hc, one_mul]

/-- A genuine positive construction in the same Sobolev space: the angular image
of any domain observable is circle-valued, with the chain-rule gradients. -/
theorem angular_graph (f : GaussianL2) (g : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph) :
    ∃ F H : GaussianL2, ∃ G K : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      (H, K) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun w => Real.cos (f w)) ∧
      H =ᵐ[gaussianProduct] (fun w => Real.sin (f w)) ∧
      G =ᵐ[gaussianProduct] (fun w => (-Real.sin (f w)) • g w) ∧
      K =ᵐ[gaussianProduct] (fun w => Real.cos (f w) • g w) ∧
      (∀ᵐ w ∂gaussianProduct, (F w) ^ 2 + (H w) ^ 2 = 1) ∧
      (∀ᵐ w ∂gaussianProduct, ‖G w‖ ^ 2 + ‖K w‖ ^ 2 = ‖g w‖ ^ 2) := by
  obtain ⟨F, G, hFG, hF, hG⟩ := GaussianClosedChainRule.bounded_closed_chain_graph f g hfg
    Real.cos (fun x => -Real.sin x) Real.hasDerivAt_cos
    Real.continuous_sin.neg 1 1 (fun x => by simpa using Real.abs_cos_le_one x)
    (fun x => by simpa using Real.abs_sin_le_one x)
  obtain ⟨H, K, hHK, hH, hK⟩ := GaussianClosedChainRule.bounded_closed_chain_graph f g hfg
    Real.sin Real.cos Real.hasDerivAt_sin Real.continuous_cos 1 1
    (fun x => by simpa using Real.abs_sin_le_one x)
    (fun x => by simpa using Real.abs_cos_le_one x)
  refine ⟨F, H, G, K, hFG, hHK, hF, hH, hG, hK, ?_, ?_⟩
  · filter_upwards [hF, hH] with w hf hh
    rw [hf, hh, add_comm]
    exact Real.sin_sq_add_cos_sq _
  · filter_upwards [hG, hK] with w hg hk
    rw [hg, hk, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs, neg_sq, ← add_mul, Real.sin_sq_add_cos_sq, one_mul]

/-- Equal-size orthogonal gradients cannot both be tangent to a unit circle,
unless they vanish.  This is pointwise Hilbert geometry, not a probability law. -/
theorem isotropic_tangent_zero (a b : ℝ) (u v : CoefficientSpace)
    (hc : a ^ 2 + b ^ 2 = 1) (ho : inner ℝ u v = 0) (hn : ‖u‖ = ‖v‖)
    (ht : a • u + b • v = 0) : u = 0 ∧ v = 0 := by
  have he := norm_add_sq_real (a • u) (b • v)
  rw [ht, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, ho] at he
  simp only [Real.norm_eq_abs, mul_pow, sq_abs, mul_zero, add_zero] at he
  rw [hn, ← add_mul, hc, one_mul] at he
  have hv : ‖v‖ = 0 := sq_eq_zero_iff.mp he.symm
  exact ⟨norm_eq_zero.mp (hn.trans hv), norm_eq_zero.mp hv⟩

/-- A circle-valued Gaussian Sobolev pair with conformal (orthogonal equal-size)
full gradients has zero gradients.  No stopping-time domain is silently added. -/
theorem circle_isotropic_zero (f h : GaussianL2) (g k : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (hhk : (h, k) ∈ closedCylindricalDerivative.graph)
    (hc : ∀ᵐ w ∂gaussianProduct, (f w) ^ 2 + (h w) ^ 2 = 1)
    (ho : ∀ᵐ w ∂gaussianProduct, inner ℝ (g w) (k w) = 0)
    (hn : ∀ᵐ w ∂gaussianProduct, ‖g w‖ = ‖k w‖) : g = 0 ∧ k = 0 := by
  have ht := circle_tangency f h g k hfg hhk hc
  have hz : ∀ᵐ w ∂gaussianProduct, g w = 0 ∧ k w = 0 := by
    filter_upwards [ht, hc, ho, hn] with w ht hc ho hn
    exact isotropic_tangent_zero _ _ _ _ hc ho hn ht
  constructor <;> apply Lp.ext
  · filter_upwards [hz, Lp.coeFn_zero CoefficientSpace 2 gaussianProduct] with w hw h0
    exact hw.1.trans h0.symm
  · filter_upwards [hz, Lp.coeFn_zero CoefficientSpace 2 gaussianProduct] with w hw h0
    exact hw.2.trans h0.symm

/-- Using the existing exact kernel theorem upgrades the geometric obstruction
to determinism, on the actual full closed derivative domain. -/
theorem circle_isotropic_constant (f h : GaussianL2) (g k : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (hhk : (h, k) ∈ closedCylindricalDerivative.graph)
    (hc : ∀ᵐ w ∂gaussianProduct, (f w) ^ 2 + (h w) ^ 2 = 1)
    (ho : ∀ᵐ w ∂gaussianProduct, inner ℝ (g w) (k w) = 0)
    (hn : ∀ᵐ w ∂gaussianProduct, ‖g w‖ = ‖k w‖) :
    (∃ a : ℝ, f =ᵐ[gaussianProduct] fun _ => a) ∧
    (∃ b : ℝ, h =ᵐ[gaussianProduct] fun _ => b) := by
  obtain ⟨hg, hk⟩ := circle_isotropic_zero f h g k hfg hhk hc ho hn
  rw [hg] at hfg
  rw [hk] at hhk
  exact ⟨(closedDerivative_zero_iff_ae_const f).mp hfg,
    (closedDerivative_zero_iff_ae_const h).mp hhk⟩

end OperatorDerivativeRewrite.Foundation.StochasticCauchyBoundaryConstraint
