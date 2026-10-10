import Foundation.FiniteGaussianTensor
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Noncircular density in independent finite Gaussian products, via one-dimensional
moment uniqueness applied to every real linear projection of positive weighted measures. -/
noncomputable section
open MeasureTheory Polynomial ProbabilityTheory
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FiniteGaussian
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]

/-- Every multivariate polynomial has every finite Gaussian moment. -/
theorem productPolynomial_memLp (p : MvPolynomial ι ℝ) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x : ι → ℝ => MvPolynomial.eval x p) r (productGaussian ι) := by
  induction p using MvPolynomial.induction_on generalizing r with
  | C a => simpa using (memLp_const a : MemLp (fun _ : ι → ℝ => a) r (productGaussian ι))
  | add p q hp hq =>
    convert (hp r hr).add (hq r hr) using 1
    ext x; simp
  | mul_X p i hp =>
    have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
    have : ENNReal.HolderTriple (2 * r) (2 * r) r := doubled_holderTriple r
    have hc := (GaussianCore.polynomial_memLp Polynomial.X (2 * r) ht).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => GaussianCore.γ) i)
    simpa [Function.eval] using
      (mul_memLp (p := 2 * r) (q := 2 * r) (r := r) (hp (2 * r) ht) hc)

/-- Actual polynomial evaluation in the independent product L² space. -/
def productPolynomialL2 (p : MvPolynomial ι ℝ) : Lp ℝ 2 (productGaussian ι) :=
  (productPolynomial_memLp p 2 (by simp)).toLp (fun x => MvPolynomial.eval x p)

theorem productPolynomialL2_coeFn (p : MvPolynomial ι ℝ) :
    productPolynomialL2 p =ᵐ[productGaussian ι] fun x => MvPolynomial.eval x p :=
  MemLp.coeFn_toLp _

/-- Linear evaluation map; its range is the algebraic polynomial core. -/
def productPolynomialEmbedding : MvPolynomial ι ℝ →ₗ[ℝ] Lp ℝ 2 (productGaussian ι) where
  toFun := productPolynomialL2
  map_add' p q := by
    apply Lp.ext
    filter_upwards [productPolynomialL2_coeFn (p + q), productPolynomialL2_coeFn p,
      productPolynomialL2_coeFn q, Lp.coeFn_add (productPolynomialL2 p) (productPolynomialL2 q)]
      with x h1 h2 h3 h4
    rw [h1, h4]; simp [h2, h3]
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [productPolynomialL2_coeFn (c • p), productPolynomialL2_coeFn p,
      Lp.coeFn_smul c (productPolynomialL2 p)] with x h1 h2 h3
    change productPolynomialL2 (c • p) x = (c • productPolynomialL2 p) x
    rw [h1, h3]; simp [h2]

private theorem realGaussian_exp_memLp (t : ℝ) (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x : ℝ => Real.exp (t * x)) r GaussianCore.γ := by
  by_cases h0 : r = 0
  · subst r; exact memLp_zero_iff_aestronglyMeasurable.mpr (by fun_prop)
  rw [← integrable_norm_rpow_iff (by fun_prop) h0 hr]
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (t * r.toReal) using 1
  funext x
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1; ring

private theorem product_exp_memLp (a : ι → ℝ) (s : Finset ι)
    (r : ℝ≥0∞) (hr : r ≠ ∞) :
    MemLp (fun x : ι → ℝ => ∏ i ∈ s, Real.exp (a i * x i)) r (productGaussian ι) := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty => simpa using (memLp_const (1 : ℝ) :
      MemLp (fun _ : ι → ℝ => (1 : ℝ)) r (productGaussian ι))
  | insert i s hi ih =>
    have ht : 2 * r ≠ ∞ := ENNReal.mul_ne_top (by simp) hr
    have : ENNReal.HolderTriple (2 * r) (2 * r) r := doubled_holderTriple r
    have hf := (realGaussian_exp_memLp (a i) (2 * r) ht).comp_measurePreserving
      (measurePreserving_eval (fun _ : ι => GaussianCore.γ) i)
    simpa [Finset.prod_insert, hi, Function.eval] using
      (mul_memLp (p := 2 * r) (q := 2 * r) (r := r) hf (ih (2 * r) ht))

/-- Exponentials of every real linear functional are square integrable. -/
theorem productGaussian_exp_linear_memLp (L : (ι → ℝ) →L[ℝ] ℝ) (t : ℝ) :
    MemLp (fun x => Real.exp (t * L x)) 2 (productGaussian ι) := by
  classical
  have he (x : ι → ℝ) : L x = ∑ i, L (Pi.single i 1) * x i := by
    rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
    apply Finset.sum_congr rfl
    intro i _
    have hh : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
      ext j; by_cases hj : j = i <;> simp [hj]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, hh, mul_comm]
  convert product_exp_memLp (fun i => t * L (Pi.single i 1)) Finset.univ 2 (by simp) using 1
  funext x
  rw [he, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  congr 1; ring

private def weightedMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ) :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

private theorem weighted_integrable_iff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {w g : Ω → ℝ} (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) :
    Integrable g (weightedMeasure μ w) ↔ Integrable (fun x => w x * g x) μ := by
  rw [weightedMeasure, integrable_withDensity_iff_integrable_smul'
    hw.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

private theorem weighted_integral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {w : Ω → ℝ} (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) (g : Ω → ℝ) :
    (∫ x, g x ∂weightedMeasure μ w) = ∫ x, w x * g x ∂μ := by
  rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul
    hw.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

private theorem weighted_finite {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {w : Ω → ℝ} (hw : Measurable w) (hn : ∀ x, 0 ≤ w x)
    (hi : Integrable w μ) : IsFiniteMeasure (weightedMeasure μ w) := by
  have hc : Integrable (fun _ : Ω => (1 : ℝ)) (weightedMeasure μ w) :=
    (weighted_integrable_iff hw hn).mpr (by simpa using hi)
  exact (integrable_const_iff.mp hc).resolve_left (by norm_num)

/-- Orthogonality to all multivariate polynomials forces an L² vector to vanish.
The argument uses positive weighted measures, one-dimensional moment uniqueness,
and characteristic-function uniqueness, rather than a density assumption. -/
theorem eq_zero_of_productPolynomial_orthogonal (f : Lp ℝ 2 (productGaussian ι))
    (hf : ∀ p : MvPolynomial ι ℝ, inner ℝ f (productPolynomialL2 p) = 0) : f = 0 := by
  classical
  let wp : (ι → ℝ) → ℝ := fun x => max (f x) 0
  let wn : (ι → ℝ) → ℝ := fun x => max (-f x) 0
  have hp : MemLp wp 2 (productGaussian ι) := (Lp.memLp f).pos_part
  have hn : MemLp wn 2 (productGaussian ι) := (Lp.memLp f).neg_part
  have hpm : Measurable wp := (Lp.stronglyMeasurable f).measurable.max measurable_const
  have hnm : Measurable wn := (Lp.stronglyMeasurable f).measurable.neg.max measurable_const
  have hpn (x) : 0 ≤ wp x := le_max_right _ _
  have hnn (x) : 0 ≤ wn x := le_max_right _ _
  let νp := weightedMeasure (productGaussian ι) wp
  let νn := weightedMeasure (productGaussian ι) wn
  have : IsFiniteMeasure νp := weighted_finite hpm hpn (hp.integrable (by simp))
  have : IsFiniteMeasure νn := weighted_finite hnm hnn (hn.integrable (by simp))
  have hproj (L : (ι → ℝ) →L[ℝ] ℝ) : νp.map L = νn.map L := by
    apply GaussianCore.finite_measure_eq_of_moments
    · intro t
      rw [integrable_map_measure (by fun_prop) (by fun_prop)]
      exact (weighted_integrable_iff hpm hpn).mpr
        (mul_L2_integrable hp (productGaussian_exp_linear_memLp L t))
    · intro t
      rw [integrable_map_measure (by fun_prop) (by fun_prop)]
      exact (weighted_integrable_iff hnm hnn).mpr
        (mul_L2_integrable hn (productGaussian_exp_linear_memLp L t))
    · intro n
      rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
        weighted_integral hpm hpn, weighted_integral hnm hnn]
      let p : MvPolynomial ι ℝ := (∑ i, MvPolynomial.C (L (Pi.single i 1)) * MvPolynomial.X i) ^ n
      have he (x : ι → ℝ) : MvPolynomial.eval x p = L x ^ n := by
        simp only [p, map_pow, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
        congr 1
        rw [← ContinuousLinearMap.sum_comp_single ℝ (fun _ : ι => ℝ) L x]
        apply Finset.sum_congr rfl
        intro i _
        have hh : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
          ext j; by_cases hj : j = i <;> simp [hj]
        simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply, hh, mul_comm]
      have hpow : MemLp (fun x => L x ^ n) 2 (productGaussian ι) :=
        by simpa only [he] using productPolynomial_memLp p 2 (by simp)
      apply sub_eq_zero.mp
      rw [← integral_sub (mul_L2_integrable hp hpow) (mul_L2_integrable hn hpow)]
      have hz := hf p
      rw [L2_inner_eq_integral] at hz
      have hae : (fun x => inner ℝ (f x) (productPolynomialL2 p x)) =ᵐ[productGaussian ι]
          fun x => wp x * L x ^ n - wn x * L x ^ n := by
        filter_upwards [productPolynomialL2_coeFn p] with x hx
        rw [hx, he, Real.inner_apply, ← sub_mul, max_zero_sub_eq_self]
      rwa [← integral_congr_ae hae]
  have hν : νp = νn := by
    apply Measure.ext_of_charFunDual
    funext L
    rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, hproj]
  have he : (fun x => ENNReal.ofReal (wp x)) =ᵐ[productGaussian ι]
      (fun x => ENNReal.ofReal (wn x)) :=
    (withDensity_eq_iff_of_sigmaFinite hpm.ennreal_ofReal.aemeasurable
      hnm.ennreal_ofReal.aemeasurable).mp hν
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := productGaussian ι)] with x hx hz
  rw [hz]
  have hw : wp x = wn x := by
    have ht := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (hpn x), ENNReal.toReal_ofReal (hnn x)] using ht
  have hh := max_zero_sub_eq_self (f x)
  change wp x - wn x = f x at hh
  rw [hw, sub_self] at hh
  exact hh.symm

/-- Multivariate polynomials are dense for every finite index type, including the empty type. -/
theorem productPolynomialEmbedding_dense :
    Dense ((productPolynomialEmbedding (ι := ι)).range : Set (Lp ℝ 2 (productGaussian ι))) := by
  have hbot : (productPolynomialEmbedding (ι := ι)).range.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    apply eq_zero_of_productPolynomial_orthogonal f
    intro p
    exact (productPolynomialEmbedding (ι := ι)).range.topologicalClosure
      |>.inner_left_of_mem_orthogonal
      ((productPolynomialEmbedding (ι := ι)).range.le_topologicalClosure ⟨p, rfl⟩) hf
  have htop := Submodule.orthogonal_eq_bot_iff.mp hbot
  rw [dense_iff_closure_eq]
  change ((productPolynomialEmbedding (ι := ι)).range.topologicalClosure :
    Set (Lp ℝ 2 (productGaussian ι))) = Set.univ
  rw [htop]; rfl

end OperatorDerivativeRewrite.Foundation.FiniteGaussian
