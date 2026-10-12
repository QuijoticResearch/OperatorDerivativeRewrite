import Foundation.GaussianSmoothIto

/-! A restricted, independently specified smooth path-functional Ito theorem:
additive cylinders of finitely many stopped Brownian observations. These need
not be terminal-only functions. Arbitrary nonlinear mixed cylinders are not claimed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianSmoothCylinders
open InfiniteGaussian GaussianTimeProcess GaussianTimeProductL2 GaussianProductDerivative
open GaussianLipschitzIntegrands GaussianPredictableFull GaussianSmoothIto

/-- A genuine smooth function of finite coordinates, independently of stochastic calculus. -/
def cylinder {n : ℕ} (f : Fin n → ℝ → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, f i (x i)

theorem cylinder_directional_hasDerivAt {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (x d : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun ε => cylinder f (fun i => x i + ε * d i))
      (∑ i, deriv (f i) (x i + a * d i) * d i) a := by
  apply HasDerivAt.fun_sum
  intro i _
  convert ((hf i (x i + a * d i)).hasDerivAt.comp a
    ((hasDerivAt_const a (x i)).add ((hasDerivAt_id a).mul_const (d i)))) using 1 <;> (try funext ε) <;> (try dsimp) <;> ring

/-- The directional Hessian is the actual derivative of the actual directional
first derivative. The diagonal form explains the absence of mixed terms. -/
theorem cylinder_second_directional_hasDerivAt {n : ℕ} (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Differentiable ℝ (deriv (f i))) (x d : Fin n → ℝ) (a : ℝ) :
    HasDerivAt (fun ε => ∑ i, deriv (f i) (x i + ε * d i) * d i)
      (∑ i, deriv (deriv (f i)) (x i + a * d i) * (d i) ^ 2) a := by
  apply HasDerivAt.fun_sum
  intro i _
  convert (((hf i (x i + a * d i)).hasDerivAt.comp a
    ((hasDerivAt_const a (x i)).add ((hasDerivAt_id a).mul_const (d i)))).mul_const (d i)) using 1 <;> (try funext ε) <;> (try dsimp) <;> ring

variable {n : ℕ} (f : Fin n → ℝ → ℝ) (r : Fin n → ℝ≥0)
  {K0 K1 K2 : Fin n → ℝ≥0}
  (h0 : ∀ i, LipschitzWith (K0 i) (f i))
  (h1 : ∀ i, LipschitzWith (K1 i) (deriv (f i)))
  (h2 : ∀ i, LipschitzWith (K2 i) (deriv (deriv (f i))))

def stoppedValue (T : ℝ≥0) : GaussianL2 := ∑ i, valueL2 (h0 i) (min T (r i))

theorem stoppedValue_coeFn (T : ℝ≥0) :
    stoppedValue f r h0 T =ᵐ[gaussianProduct] fun ω =>
      cylinder f (fun i => process (min T (r i)) ω) := by
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => valueL2 (h0 i) (min T (r i))),
    ae_all_iff.mpr (fun i => valueL2_coeFn (h0 i) (min T (r i)))] with ω hs hi
  change stoppedValue f r h0 T ω = _ at hs
  rw [hs]
  simp only [Finset.sum_apply, hi, cylinder]

def stoppedIntegrand (T : ℝ≥0) : fullPredictable := ∑ i, integrand (h1 i) (min T (r i))

theorem stoppedIntegrand_slices (T : ℝ≥0) :
    scalarCurry (stoppedIntegrand f r h1 T : TimeProbabilityL2) =ᵐ[volume]
      (Ioc 0 (T : ℝ)).indicator (fun t => ∑ i,
        (Ioc 0 (r i : ℝ)).indicator (fun _ => valueL2 (h1 i) t.toNNReal) t) := by
  change scalarCurry (↑(∑ i, integrand (h1 i) (min T (r i)))) =ᵐ[volume] _
  rw [Submodule.coe_sum, map_sum]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
    scalarCurry (integrand (h1 i) (min T (r i)) : TimeProbabilityL2)),
    ae_all_iff.mpr (fun i => integrand_slices (h1 i) (min T (r i)))] with t hs hi
  rw [hs]
  simp only [Finset.sum_apply, hi, NNReal.coe_min]
  by_cases ht : t ∈ Ioc 0 (T : ℝ)
  · rw [indicator_of_mem ht]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hr : t ∈ Ioc 0 (r i : ℝ)
    · rw [indicator_of_mem (show t ∈ Ioc 0 (min (T : ℝ) (r i : ℝ)) from
        ⟨ht.1, le_min ht.2 hr.2⟩), indicator_of_mem hr]
    · have hm : t ∉ Ioc 0 (min (T : ℝ) (r i : ℝ)) :=
        fun hh => hr ⟨hh.1, hh.2.trans (min_le_right _ _)⟩
      simp [hr, hm]
  · rw [indicator_of_notMem ht]
    apply Finset.sum_eq_zero
    intro i _
    exact indicator_of_notMem (fun hh => ht ⟨hh.1, hh.2.trans (min_le_left _ _)⟩) _

/-- The correction is specified by actual second derivatives before the identity. -/
def stoppedDrift (T : ℝ≥0) : GaussianL2 :=
  ∑ i, ∫ t in 0..(min T (r i) : ℝ≥0), valueL2 (h2 i) t.toNNReal

/-- Corrected path-functional Ito for additive stopped-observation cylinders.
Each f_i is C3, Lipschitz together with its first two derivatives, with bounded
third derivative. Empty, repeated and zero observation times are allowed. -/
theorem stopped_cylinder_ito (hf : ∀ i, ContDiff ℝ 3 (f i))
    (M : Fin n → ℝ) (hM : ∀ i x, ‖iteratedDeriv 3 (f i) x‖ ≤ M i) (T : ℝ≥0) :
    stoppedValue f r h0 T - stoppedValue f r h0 0 =
      itoIntegral (stoppedIntegrand f r h1 T) + (1 / 2 : ℝ) • stoppedDrift f r h2 T := by
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl
    (fun i _ => ito_of_lipschitz_derivatives (f i) (hf i) (h0 i) (h1 i) (h2 i)
      (M i) (hM i) (min T (r i)))
  simpa only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← map_sum, ← Finset.smul_sum,
    stoppedValue, stoppedIntegrand, stoppedDrift, min_zero, zero_min] using he

end OperatorDerivativeRewrite.Foundation.GaussianSmoothCylinders


