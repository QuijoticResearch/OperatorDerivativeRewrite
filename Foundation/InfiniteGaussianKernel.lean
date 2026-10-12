import Foundation.InfiniteGaussianProjectionConvergence
import Foundation.FiniteGaussianKernel

/-!
# Constant kernel of the genuine infinite Gaussian derivative

The proof restricts an actual zero-gradient graph pair to each finite sector,
uses the complete finite Hermite basis, and passes through the already proved
strong convergence of scalar sector projections. No Brownian filtration or
stochastic-integral sensitivity identity is assumed or asserted here.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian

/-- The constant one as an actual Gaussian polynomial L² class. -/
def gaussianOne : GaussianL2 := coordinatePolynomialL2 1

theorem gaussianOne_coeFn : gaussianOne =ᵐ[gaussianProduct] fun _ => (1 : ℝ) := by
  simpa [gaussianOne] using coordinatePolynomialL2_coeFn 1

/-- Every finite-sector vacuum lifts to the same constant L² random variable. -/
theorem finitePullback_vacuum (s : Finset ℕ) :
    finitePullback s (FiniteGaussian.tensorHermite (fun _ : s => 0)) = gaussianOne := by
  apply Lp.ext
  have hv := (finiteProjection_measurePreserving s).quasiMeasurePreserving.ae
    (FiniteGaussian.tensorHermite_zero_coeFn (ι := s))
  filter_upwards [finitePullback_coeFn s
    (FiniteGaussian.tensorHermite (fun _ : s => 0)), hv, gaussianOne_coeFn] with ω hp hv h1
  exact hp.trans (hv.trans h1.symm)

/-- Pairing with the vacuum is the genuine integrable expectation. -/
theorem gaussianOne_inner_eq_integral (f : GaussianL2) :
    inner ℝ gaussianOne f = ∫ ω, f ω ∂gaussianProduct := by
  rw [L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [gaussianOne_coeFn] with ω h1
  simp [h1]

/-- A zero-gradient pair projects to its constant coefficient in every finite sector. -/
theorem finiteScalarProjection_of_closedDerivative_zero (s : Finset ℕ) (f : GaussianL2)
    (hf : (f, (0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph) :
    finiteScalarProjection s f = inner ℝ gaussianOne f • gaussianOne := by
  have ha : (f, (0 : GaussianVectorL2)) ∈ cylindricalDivergence.adjoint.graph := by
    rwa [cylindricalDivergence_adjoint_eq_closedDerivative]
  have hs := finiteSector_weak_gradient_graph s f 0 ha
  have hg : (((finitePullback s).toContinuousLinearMap.adjoint f),
      (0 : FiniteGaussian.VectorGaussianL2 s)) ∈ FiniteGaussian.closedGradient.graph := by
    simpa only [map_zero, FiniteGaussian.closedGradient_eq_divergence_adjoint] using hs
  have he := (FiniteGaussian.closedGradient_zero_iff_vacuum _).mp hg
  change finitePullback s ((finitePullback s).toContinuousLinearMap.adjoint f) = _
  rw [he, map_smul, finitePullback_vacuum]
  congr 1
  change inner ℝ (FiniteGaussian.tensorHermite (fun _ : s => 0))
    ((finitePullback s).toContinuousLinearMap.adjoint f) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact congrArg (fun v : GaussianL2 => inner ℝ v f) (finitePullback_vacuum s)

/-- Constants belong to the actual closed derivative domain and have value zero. -/
theorem closedDerivative_constant_graph (c : ℝ) :
    (c • gaussianOne, (0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph := by
  let s : Finset ℕ := ∅
  have hg : (c • FiniteGaussian.tensorHermite (fun _ : s => 0),
      (0 : FiniteGaussian.VectorGaussianL2 s)) ∈ FiniteGaussian.closedGradient.graph :=
    (FiniteGaussian.closedGradient_zero_iff_const _).2 ⟨c, rfl⟩
  rw [FiniteGaussian.closedGradient_eq_divergence_adjoint] at hg
  have hl := finiteGradient_lift_closed_graph s _ _ hg
  simpa only [map_smul, map_zero, finitePullback_vacuum] using hl

/-- The kernel of the full infinite-dimensional closed Gaussian derivative is
exactly its one-dimensional vacuum space. Both graph membership and value are proved. -/
theorem closedDerivative_zero_iff_vacuum (f : GaussianL2) :
    (f, (0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph ↔
      f = inner ℝ gaussianOne f • gaussianOne := by
  constructor
  · intro hf
    apply tendsto_nhds_unique (finiteScalarProjection_range_tendsto f)
    simpa only [finiteScalarProjection_of_closedDerivative_zero _ _ hf] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => inner ℝ gaussianOne f • gaussianOne)
        atTop (𝓝 (inner ℝ gaussianOne f • gaussianOne)))
  · intro hf
    rw [hf]
    exact closedDerivative_constant_graph _

/-- Zero derivative is equivalent to an ordinary deterministic representative,
not an independence assumption against arbitrary random test fields. -/
theorem closedDerivative_zero_iff_ae_const (f : GaussianL2) :
    (f, (0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph ↔
      ∃ c : ℝ, f =ᵐ[gaussianProduct] fun _ => c := by
  constructor
  · intro hf
    refine ⟨inner ℝ gaussianOne f, ?_⟩
    have he := (closedDerivative_zero_iff_vacuum f).mp hf
    filter_upwards [Lp.coeFn_smul (inner ℝ gaussianOne f) gaussianOne,
      gaussianOne_coeFn] with ω hs h1
    calc
      f ω = (inner ℝ gaussianOne f • gaussianOne : GaussianL2) ω :=
        congrArg (fun v : GaussianL2 => v ω) he
      _ = inner ℝ gaussianOne f := by
        simp only [hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]
  · rintro ⟨c, hc⟩
    have he : f = c • gaussianOne := by
      apply Lp.ext
      filter_upwards [hc, Lp.coeFn_smul c gaussianOne, gaussianOne_coeFn] with ω hf hs h1
      simp only [hf, hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]
    rw [he]
    exact closedDerivative_constant_graph c

/-- The deterministic value in the zero-gradient theorem is exactly the expectation. -/
theorem closedDerivative_zero_iff_ae_mean (f : GaussianL2) :
    (f, (0 : GaussianVectorL2)) ∈ closedCylindricalDerivative.graph ↔
      f =ᵐ[gaussianProduct] fun _ => ∫ ω, f ω ∂gaussianProduct := by
  constructor
  · intro hf
    have he := (closedDerivative_zero_iff_vacuum f).mp hf
    rw [gaussianOne_inner_eq_integral] at he
    have hc : (∫ ω, f ω ∂gaussianProduct) • gaussianOne =ᵐ[gaussianProduct]
        fun _ => ∫ ω, f ω ∂gaussianProduct := by
      filter_upwards [Lp.coeFn_smul (∫ ω, f ω ∂gaussianProduct) gaussianOne,
        gaussianOne_coeFn] with ω hs h1
      simp only [hs, Pi.smul_apply, h1, smul_eq_mul, mul_one]
    filter_upwards [hc] with ω hω
    exact (congrArg (fun v : GaussianL2 => v ω) he).trans hω
  · intro hf
    exact (closedDerivative_zero_iff_ae_const f).2 ⟨_, hf⟩

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
