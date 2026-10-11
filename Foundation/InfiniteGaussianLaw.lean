import Foundation.InfiniteGaussianFirstChaos
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Measure.LevyConvergence

/-! Exact Gaussian laws for the genuine first-chaos L² limits. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

/-- Actual finite weighted coordinate sum. -/
def weightedSum (a : ℕ → ℝ) (s : Finset ℕ) (ω : SampleSpace) : ℝ :=
  ∑ n ∈ s, a n * coordinate n ω

/-- Its actual square-integrable class. -/
def weightedSumL2 (a : ℕ → ℝ) (s : Finset ℕ) : GaussianL2 :=
  ∑ n ∈ s, a n • coordinateL2 n

theorem weightedSumL2_coeFn (a : ℕ → ℝ) (s : Finset ℕ) :
    weightedSumL2 a s =ᵐ[gaussianProduct] weightedSum a s := by
  have hc (n : ℕ) : (a n • coordinateL2 n : GaussianL2) =ᵐ[gaussianProduct]
      fun ω => a n * coordinate n ω := by
    filter_upwards [Lp.coeFn_smul (a n) (coordinateL2 n), coordinateL2_coeFn n] with ω hs hn
    simp [hs, hn, smul_eq_mul]
  filter_upwards [Lp.coeFn_finsetSum s (fun n => a n • coordinateL2 n),
    ae_all_iff.2 hc] with ω hs ha
  simp only [Finset.sum_apply] at hs
  change (∑ n ∈ s, a n • coordinateL2 n : GaussianL2) ω = _
  rw [hs]
  exact Finset.sum_congr rfl (fun n _ => ha n)

/-- Exact characteristic function of a finite weighted sum. -/
theorem weightedSum_charFun (a : ℕ → ℝ) (s : Finset ℕ) (t : ℝ) :
    charFun (gaussianProduct.map (weightedSum a s)) t =
      Complex.exp (-((∑ n ∈ s, a n ^ 2 : ℝ) : ℂ) * t ^ 2 / 2) := by
  classical
  have hi := coordinates_independent.comp (fun n x => a n * x) (by fun_prop)
  have hf := (hi.restrict s).charFun_map_fun_finsetSum_eq_prod
    (fun n _ => ((measurable_const.mul (coordinate_measurePreserving n).measurable)).aemeasurable)
  have hl (n : ℕ) : gaussianProduct.map ((fun _ : SampleSpace => a n) * coordinate n) =
      gaussianReal 0 (NNReal.mk (a n ^ 2) (sq_nonneg _)) := by
    change gaussianProduct.map ((fun x : ℝ => a n * x) ∘ coordinate n) = _
    have hm : Measurable (fun x : ℝ => a n * x) := measurable_const.mul measurable_id
    rw [← Measure.map_map hm
      (coordinate_measurePreserving n).measurable,
      coordinate_law]
    exact GaussianCore.W_gaussian_law (a n)
  change charFun (gaussianProduct.map (fun ω => ∑ n ∈ s, a n * coordinate n ω)) t = _
  have hf₁ := congrFun hf t
  simp only [Pi.mul_apply] at hf₁
  rw [hf₁]
  simp only [Finset.prod_apply]
  simp_rw [hl]
  simp_rw [charFun_gaussianReal]
  rw [← Complex.exp_sum]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, zero_sub, NNReal.coe_mk,
    Complex.ofReal_sum, Complex.ofReal_pow]
  congr 1
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  ring

/-- The finite sums have exact centered Gaussian laws, also for empty sums or zero weights. -/
theorem weightedSum_law (a : ℕ → ℝ) (s : Finset ℕ) :
    gaussianProduct.map (weightedSum a s) = gaussianReal 0
      (NNReal.mk (∑ n ∈ s, a n ^ 2) (Finset.sum_nonneg (fun n _ => sq_nonneg (a n)))) := by
  apply Measure.ext_of_charFun
  ext t
  rw [weightedSum_charFun, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- The verified L² convergence of finite weighted sums. -/
theorem weightedSumL2_tendsto (h : CoefficientSpace) :
    Tendsto (fun N => weightedSumL2 h (Finset.range N)) atTop
      (𝓝 (firstChaosEmbedding h)) :=
  (firstChaos_hasSum h).tendsto_sum_nat

/-- L² convergence implies convergence in probability by Mathlib's quantitative Lp theorem. -/
theorem weightedSumL2_tendstoInMeasure (h : CoefficientSpace) :
    TendstoInMeasure gaussianProduct (fun N => weightedSumL2 h (Finset.range N)) atTop
      (firstChaosEmbedding h) :=
  tendstoInMeasure_of_tendsto_Lp (weightedSumL2_tendsto h)

/-- The L² approximants converge in distribution; this implication is explicitly justified. -/
theorem weightedSumL2_tendstoInDistribution (h : CoefficientSpace) :
    TendstoInDistribution (fun N => (weightedSumL2 h (Finset.range N) : SampleSpace → ℝ))
      atTop (firstChaosEmbedding h) (fun _ => gaussianProduct) gaussianProduct :=
  (weightedSumL2_tendstoInMeasure h).tendstoInDistribution_of_aemeasurable
    (fun _ => (Lp.stronglyMeasurable _).aemeasurable)
    (Lp.stronglyMeasurable _).aemeasurable

/-- Square-summable coefficient energy converges to the squared ℓ² norm. -/
theorem coefficientSquares_hasSum (h : CoefficientSpace) :
    HasSum (fun n => h n ^ 2) (‖h‖ ^ 2) := by
  simpa [Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) h

/-- Exact limiting characteristic function, deduced from distributional convergence. -/
theorem firstChaos_charFun (h : CoefficientSpace) (t : ℝ) :
    charFun (gaussianProduct.map (firstChaosEmbedding h)) t =
      Complex.exp (-(‖h‖ ^ 2 : ℝ) * t ^ 2 / 2) := by
  have hc := (weightedSumL2_tendstoInDistribution h).tendsto_charFun t
  have he : Tendsto (fun N => Complex.exp
      (-((∑ n ∈ Finset.range N, h n ^ 2 : ℝ) : ℂ) * t ^ 2 / 2)) atTop
      (𝓝 (Complex.exp (-(‖h‖ ^ 2 : ℝ) * t ^ 2 / 2))) := by
    exact (((coefficientSquares_hasSum h).tendsto_sum_nat.ofReal.neg.mul_const
      ((t : ℂ) ^ 2)).div_const 2).cexp
  have hc' : Tendsto (fun N => Complex.exp
      (-((∑ n ∈ Finset.range N, h n ^ 2 : ℝ) : ℂ) * t ^ 2 / 2)) atTop
      (𝓝 (charFun (gaussianProduct.map (firstChaosEmbedding h)) t)) := by
    convert hc using 1
    ext N
    rw [Measure.map_congr (weightedSumL2_coeFn h (Finset.range N)), weightedSum_charFun]
  exact tendsto_nhds_unique hc' he

/-- The actual L² limit has the exact centered Gaussian law, even for h = 0. -/
theorem firstChaos_law (h : CoefficientSpace) :
    gaussianProduct.map (firstChaosEmbedding h) =
      gaussianReal 0 (NNReal.mk (‖h‖ ^ 2) (sq_nonneg _)) := by
  apply Measure.ext_of_charFun
  ext t
  rw [firstChaos_charFun, charFun_gaussianReal]
  congr 1
  push_cast
  ring

/-- Gaussianity is a theorem about the actual random variable, not prescribed data. -/
theorem firstChaos_hasGaussianLaw (h : CoefficientSpace) :
    HasGaussianLaw (firstChaosEmbedding h) gaussianProduct := by
  have hl : HasLaw (firstChaosEmbedding h)
      (gaussianReal 0 (NNReal.mk (‖h‖ ^ 2) (sq_nonneg _))) gaussianProduct :=
    ⟨(Lp.stronglyMeasurable _).aemeasurable, firstChaos_law h⟩
  exact hl.hasGaussianLaw

end OperatorDerivativeRewrite.Foundation.InfiniteGaussian
