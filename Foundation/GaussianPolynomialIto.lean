import Foundation.GaussianPolynomialProcess

/-! Arbitrary bivariate polynomial Itô for the existing predictable stochastic integral.
The spatial field is defined independently by actual polynomial differentiation and L² membership. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set MvPolynomial
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianPolynomialIto
open InfiniteGaussian GaussianPolynomialHeat GaussianPolynomialProcess GaussianTimeSpaceHermite
open GaussianHermiteRepresentation GaussianHermiteIntegrand GaussianWeightedTimeHermite
open GaussianHermiteTimeKernel GaussianPredictableFull GaussianTimeProductL2 GaussianProductDerivative
open GaussianBochnerDerivative

def spatialValue (T : ℝ≥0) (p : SpaceTimePolynomial) : TimeScalarL2 :=
  (continuous_interval_memLp
    (fun t => valueL2 t.toNNReal (pderiv 1 p))
    ((valueL2_continuous (pderiv 1 p)).comp continuous_real_toNNReal) T).toLp _

theorem spatialValue_coeFn (T : ℝ≥0) (p : SpaceTimePolynomial) :
    spatialValue T p =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator
      (fun t => valueL2 t.toNNReal (pderiv 1 p)) := MemLp.coeFn_toLp _

def spatialField (T : ℝ≥0) : SpaceTimePolynomial →ₗ[ℝ] TimeScalarL2 where
  toFun := spatialValue T
  map_add' p q := by
    apply Lp.ext
    filter_upwards [spatialValue_coeFn T (p + q), spatialValue_coeFn T p,
      spatialValue_coeFn T q, Lp.coeFn_add (spatialValue T p) (spatialValue T q)] with x ha hp hq hs
    rw [ha, hs]
    simp only [Pi.add_apply, hp, hq]
    by_cases hx : x ∈ Ioc 0 (T : ℝ) <;> simp [hx]
  map_smul' c p := by
    apply Lp.ext
    simp only [RingHom.id_apply]
    filter_upwards [spatialValue_coeFn T (c • p), spatialValue_coeFn T p,
      Lp.coeFn_smul c (spatialValue T p)] with x hc hp hs
    rw [hc, hs]
    simp only [Pi.smul_apply, hp]
    by_cases hx : x ∈ Ioc 0 (T : ℝ) <;> simp [hx, Derivation.map_smul]

theorem spatialField_coeFn (T : ℝ≥0) (p : SpaceTimePolynomial) :
    spatialField T p =ᵐ[volume] (Ioc 0 (T : ℝ)).indicator
      (fun t => valueL2 t.toNNReal (pderiv 1 p)) := spatialValue_coeFn T p

theorem basis_representation (T : ℝ≥0) (k n : ℕ) :
    ∃ U : fullPredictable, scalarCurry (U : TimeProbabilityL2) = spatialField T (basisPolynomial (k, n)) ∧
      itoIntegral U = noiseTarget T (basisPolynomial (k, n)) := by
  cases n with
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · change scalarCurry (0 : TimeProbabilityL2) = _
      rw [map_zero]
      apply Lp.ext
      filter_upwards [Lp.coeFn_zero GaussianL2 2 volume, spatialField_coeFn T (basisPolynomial (k, 0))]
        with x hz hx
      simp [hz, hx, basis_spatial_zero]
    · rw [map_zero, noiseTarget_basis_zero]
  | succ n =>
    let a : ℝ → ℝ := fun t => t ^ k
    let q : ℝ → ℝ := fun t => (k : ℝ) * t ^ (k - 1)
    have hq : Continuous q := continuous_const.mul (continuous_id.pow _)
    have haq (t : ℝ) : HasDerivAt a (q t) t := by
      exact hasDerivAt_pow k t
    refine ⟨(n + 1 : ℝ) • weightedIntegrand a q n T, ?_, ?_⟩
    · change scalarCurry ((n + 1 : ℝ) • (weightedIntegrand a q n T : TimeProbabilityL2)) = _
      rw [map_smul]
      apply Lp.ext
      filter_upwards [Lp.coeFn_smul (n + 1 : ℝ) (scalarCurry (weightedIntegrand a q n T)),
        weightedIntegrand_slices a q hq haq n T,
        spatialField_coeFn T (basisPolynomial (k, n + 1))] with x hs hw hp
      rw [hs, hp]
      change (n + 1 : ℝ) • scalarCurry (weightedIntegrand a q n T : TimeProbabilityL2) x = _
      rw [hw]
      by_cases hx : x ∈ Ioc 0 (T : ℝ)
      · simp only [indicator_of_mem hx, basis_spatial_succ, map_smul, valueL2_basis,
          Real.coe_toNNReal _ hx.1.le, a]
      · simp [hx]
    · change itoIntegral ((n + 1 : ℝ) • weightedIntegrand a q n T) = _
      rw [map_smul]
      have hi := weighted_hermite_identity a q hq n T
      change _ = valueL2 T _ - valueL2 0 _ - timeIntegral T (heat _)
      rw [valueL2_basis, valueL2_basis, brownianCore_zero_time, smul_zero, sub_zero,
        timeIntegral_basis_heat]
      change (n + 1 : ℝ) • itoIntegral (weightedIntegrand a q n T) =
        a T • (brownianCore T (n + 1) : GaussianL2) -
          ∫ t in 0..(T : ℝ), q t • (brownianCore t.toNNReal (n + 1) : GaussianL2)
      rw [hi]
      module

theorem polynomial_representation (T : ℝ≥0) (p : SpaceTimePolynomial) :
    ∃ U : fullPredictable, scalarCurry (U : TimeProbabilityL2) = spatialField T p ∧
      itoIntegral U = noiseTarget T p := by
  have hp : p ∈ Submodule.span ℝ (Set.range basisPolynomial) := by rw [basisPolynomial_span]; trivial
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨⟨k,n⟩, rfl⟩ := hp; exact basis_representation T k n
  | zero => exact ⟨0, by simp, by simp⟩
  | add p q hp hq ihp ihq =>
    obtain ⟨U, hU, hJU⟩ := ihp
    obtain ⟨V, hV, hJV⟩ := ihq
    refine ⟨U + V, ?_, ?_⟩
    · change scalarCurry ((U : TimeProbabilityL2) + (V : TimeProbabilityL2)) = _
      rw [map_add, map_add, hU, hV]
    · rw [map_add, map_add, hJU, hJV]
  | smul c p hp ih =>
    obtain ⟨U, hU, hJU⟩ := ih
    refine ⟨c • U, ?_, ?_⟩
    · change scalarCurry (c • (U : TimeProbabilityL2)) = _
      rw [map_smul, map_smul, hU]
    · rw [map_smul, map_smul, hJU]

/-- Full time-dependent polynomial Itô in genuine Gaussian L², with the actual spatial
polynomial derivative as the independently specified integrand and the normalized heat drift. -/
theorem polynomial_ito (T : ℝ≥0) (p : SpaceTimePolynomial) :
    ∃! U : fullPredictable,
      (scalarCurry (U : TimeProbabilityL2) = spatialField T p) ∧
      valueL2 T p - valueL2 0 p = itoIntegral U +
        ∫ t in 0..(T : ℝ), valueL2 t.toNNReal (heat p) := by
  obtain ⟨U, hU, hJU⟩ := polynomial_representation T p
  refine ⟨U, ⟨hU, ?_⟩, ?_⟩
  · rw [hJU, noiseTarget_apply]; module
  · intro V hV
    apply Subtype.ext
    exact scalarCurry.injective (hV.1.trans hU.symm)

end OperatorDerivativeRewrite.Foundation.GaussianPolynomialIto
