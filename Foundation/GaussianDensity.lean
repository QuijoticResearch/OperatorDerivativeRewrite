import Foundation.GaussianOperator
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-! Polynomial density from exponential moments, independent of operator adjoints. -/
noncomputable section
open MeasureTheory ProbabilityTheory Polynomial
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianCore
set_option backward.isDefEq.respectTransparency false

/-- Finite real measures with all exponential moments are determined by their moments. -/
theorem finite_measure_eq_of_moments {μ ν : Measure ℝ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ t : ℝ, Integrable (fun x => Real.exp (t * x)) μ)
    (hν : ∀ t : ℝ, Integrable (fun x => Real.exp (t * x)) ν)
    (hm : ∀ n : ℕ, (∫ x, x ^ n ∂μ) = ∫ x, x ^ n ∂ν) : μ = ν := by
  have hsetμ : integrableExpSet id μ = Set.univ := Set.eq_univ_of_forall hμ
  have hsetν : integrableExpSet id ν = Set.univ := Set.eq_univ_of_forall hν
  have haμ (z : ℂ) : AnalyticAt ℂ (complexMGF id μ) z :=
    analyticAt_complexMGF (by simp [hsetμ])
  have haν (z : ℂ) : AnalyticAt ℂ (complexMGF id ν) z :=
    analyticAt_complexMGF (by simp [hsetν])
  have hd (n : ℕ) : iteratedDeriv n (complexMGF id μ) 0 =
      iteratedDeriv n (complexMGF id ν) 0 := by
    rw [iteratedDeriv_complexMGF (by simp [hsetμ]),
      iteratedDeriv_complexMGF (by simp [hsetν])]
    simp only [id_eq, zero_mul, Complex.exp_zero, mul_one, ← Complex.ofReal_pow]
    norm_cast
    exact hm n
  apply Measure.ext_of_complexMGF_id_eq
  funext z
  rw [← Complex.taylorSeries_eq_of_entire' (fun z => (haμ z).differentiableAt)
      (c := 0) (z := z),
    ← Complex.taylorSeries_eq_of_entire' (fun z => (haν z).differentiableAt)
      (c := 0) (z := z)]
  simp only [hd]

/-- Gaussian exponential functions themselves belong to L², not merely L¹. -/
theorem gaussian_exp_memLp_two (t : ℝ) :
    MemLp (fun x : ℝ => Real.exp (t * x)) 2 γ := by
  rw [← integrable_norm_rpow_iff (by fun_prop) (by simp) (by simp)]
  convert integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (2 * t) using 1
  funext x
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Real.rpow_two]
  rw [sq, ← Real.exp_add]
  congr 1; ring

/-- A nonnegative real density defines an ordinary positive measure. -/
def weightedMeasure (μ : Measure ℝ) (w : ℝ → ℝ) : Measure ℝ :=
  μ.withDensity (fun x => ENNReal.ofReal (w x))

/-- Exact integrability transfer for nonnegative real densities. -/
theorem weighted_integrable_iff {μ : Measure ℝ} {w g : ℝ → ℝ}
    (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) :
    Integrable g (weightedMeasure μ w) ↔ Integrable (fun x => w x * g x) μ := by
  rw [weightedMeasure, integrable_withDensity_iff_integrable_smul'
    hw.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

/-- Exact integral transfer, including the integrability conventions of Bochner integration. -/
theorem weighted_integral {μ : Measure ℝ} {w : ℝ → ℝ}
    (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) (g : ℝ → ℝ) :
    (∫ x, g x ∂weightedMeasure μ w) = ∫ x, w x * g x ∂μ := by
  rw [weightedMeasure, integral_withDensity_eq_integral_toReal_smul
    hw.ennreal_ofReal (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hn _), smul_eq_mul]

/-- Integrable nonnegative densities yield finite measures. -/
theorem weighted_finite {μ : Measure ℝ} {w : ℝ → ℝ}
    (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) (hi : Integrable w μ) :
    IsFiniteMeasure (weightedMeasure μ w) := by
  have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (weightedMeasure μ w) :=
    (weighted_integrable_iff hw hn).mpr (by simpa using hi)
  exact (integrable_const_iff.mp hc).resolve_left (by norm_num)

/-- An L² function orthogonal to every Gaussian polynomial is zero. -/
theorem eq_zero_of_polynomial_orthogonal (f : GaussianL2)
    (hf : ∀ p : ℝ[X], inner ℝ f (polynomialL2 p) = 0) : f = 0 := by
  let wp : ℝ → ℝ := fun x => max (f x) 0
  let wn : ℝ → ℝ := fun x => max (-f x) 0
  have hp : MemLp wp 2 γ := (Lp.memLp f).pos_part
  have hn : MemLp wn 2 γ := (Lp.memLp f).neg_part
  have hpm : Measurable wp := (Lp.stronglyMeasurable f).measurable.max measurable_const
  have hnm : Measurable wn := (Lp.stronglyMeasurable f).measurable.neg.max measurable_const
  have hpn (x) : 0 ≤ wp x := le_max_right _ _
  have hnn (x) : 0 ≤ wn x := le_max_right _ _
  let νp := weightedMeasure γ wp
  let νn := weightedMeasure γ wn
  have : IsFiniteMeasure νp := weighted_finite hpm hpn (hp.integrable (by simp))
  have : IsFiniteMeasure νn := weighted_finite hnm hnn (hn.integrable (by simp))
  have hm0 (n : ℕ) : (∫ x, f x * x ^ n ∂γ) = 0 := by
    have ht := hf (Polynomial.X ^ n)
    rw [L2_inner_eq_integral] at ht
    have he : (∫ x, inner ℝ (f x) (polynomialL2 (Polynomial.X ^ n) x) ∂γ) =
        ∫ x, f x * x ^ n ∂γ := by
      apply integral_congr_ae
      filter_upwards [polynomialL2_coeFn (Polynomial.X ^ n)] with x hx
      rw [hx]; simp [mul_comm]
    rwa [he] at ht
  have hν : νp = νn := by
    apply finite_measure_eq_of_moments
    · intro t
      exact (weighted_integrable_iff hpm hpn).mpr
        (mul_L2_integrable hp (gaussian_exp_memLp_two t))
    · intro t
      exact (weighted_integrable_iff hnm hnn).mpr
        (mul_L2_integrable hn (gaussian_exp_memLp_two t))
    · intro n
      rw [weighted_integral hpm hpn, weighted_integral hnm hnn]
      have hpow := polynomial_memLp (Polynomial.X ^ n) 2 (by simp)
      have hpi : Integrable (fun x => wp x * x ^ n) γ := by
        convert mul_L2_integrable hp hpow using 1
        funext x; simp
      have hni : Integrable (fun x => wn x * x ^ n) γ := by
        convert mul_L2_integrable hn hpow using 1
        funext x; simp
      apply sub_eq_zero.mp
      rw [← integral_sub hpi hni]
      convert hm0 n using 1
      congr 1; funext x
      rw [← sub_mul, max_zero_sub_eq_self]
  have he : (fun x => ENNReal.ofReal (wp x)) =ᵐ[γ] (fun x => ENNReal.ofReal (wn x)) :=
    (withDensity_eq_iff_of_sigmaFinite hpm.ennreal_ofReal.aemeasurable
      hnm.ennreal_ofReal.aemeasurable).mp hν
  apply Lp.ext
  filter_upwards [he, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := γ)] with x hx hz
  rw [hz]
  have hw : wp x = wn x := by
    have ht := congrArg ENNReal.toReal hx
    simpa only [ENNReal.toReal_ofReal (hpn x), ENNReal.toReal_ofReal (hnn x)] using ht
  have hh := max_zero_sub_eq_self (f x)
  change wp x - wn x = f x at hh
  rw [hw, sub_self] at hh
  exact hh.symm

/-- Polynomials are dense in Gaussian L², without using any operator identity. -/
theorem polynomialEmbedding_dense : Dense (polynomialEmbedding.range : Set GaussianL2) := by
  have hbot : polynomialEmbedding.range.topologicalClosureᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro f hf
    apply eq_zero_of_polynomial_orthogonal f
    intro p
    exact polynomialEmbedding.range.topologicalClosure.inner_left_of_mem_orthogonal
      (polynomialEmbedding.range.le_topologicalClosure ⟨p, rfl⟩) hf
  have htop := Submodule.orthogonal_eq_bot_iff.mp hbot
  rw [dense_iff_closure_eq]
  change (polynomialEmbedding.range.topologicalClosure : Set GaussianL2) = Set.univ
  rw [htop]; rfl

end OperatorDerivativeRewrite.Foundation.GaussianCore
