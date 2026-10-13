import Foundation.FractionalSpectralGeometry
import Foundation.GaussianDeterministicIntegral

/-! A concrete centered Gaussian realization with the fractional Brownian covariance.
Its deterministic integrand space is an independently constructed closed Hilbert span.
No sample-path version, causal Brownian representation, or fractional Clark--Ocone
formula is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FractionalGaussianProcess
open FractionalSpectralKernel FractionalSpectralGeometry GaussianHilbertProcess
open InfiniteGaussian SeparableHilbertEmbedding GaussianTimeFieldNorm GaussianTimePolynomialPairing
attribute [local instance] spectralSpace_secondCountable

variable (H : ℝ) (hH0 : 0 < H) (hH1 : H < 1)

def integrandSpace : Submodule ℝ SpectralSpace :=
  (Submodule.span ℝ (range (fun t : ℝ≥0 => normalized H hH0 hH1 t))).topologicalClosure

theorem integrandSpace_isClosed : IsClosed (integrandSpace H hH0 hH1 : Set SpectralSpace) :=
  Submodule.isClosed_topologicalClosure _

instance integrandSpace_complete : CompleteSpace (integrandSpace H hH0 hH1) :=
  (integrandSpace_isClosed H hH0 hH1).completeSpace_coe

def kernelVector (t : ℝ≥0) : integrandSpace H hH0 hH1 :=
  ⟨normalized H hH0 hH1 t,
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, rfl⟩)⟩

theorem kernelVector_inner (s t : ℝ≥0) :
    inner ℝ (kernelVector H hH0 hH1 s) (kernelVector H hH0 hH1 t) =
      ((s:ℝ)^(2*H) + (t:ℝ)^(2*H) - |(t:ℝ)-s|^(2*H)) / 2 := by
  change inner ℝ (normalized H hH0 hH1 s) (normalized H hH0 hH1 t) = _
  rw [normalized_inner]
  simp only [FractionalSpectralGeometry.covariance, abs_of_nonneg s.coe_nonneg, abs_of_nonneg t.coe_nonneg]

def cameronMartinFunction (v : integrandSpace H hH0 hH1) (t : ℝ≥0) : ℝ :=
  inner ℝ (v : SpectralSpace) (normalized H hH0 hH1 t)

theorem cameronMartin_increment_bound (v : integrandSpace H hH0 hH1) (s t : ℝ≥0) :
    |cameronMartinFunction H hH0 hH1 v t - cameronMartinFunction H hH0 hH1 v s| ≤
      ‖v‖ * |(t:ℝ)-s|^H := by
  rw [cameronMartinFunction, cameronMartinFunction, ← inner_sub_right]
  simpa only [normalized_sub_norm, Submodule.norm_coe] using
    abs_real_inner_le_norm (v : SpectralSpace) (normalized H hH0 hH1 t - normalized H hH0 hH1 s)

theorem cameronMartinFunction_injective : Function.Injective (cameronMartinFunction H hH0 hH1) := by
  intro v w he
  let z : SpectralSpace := (v : SpectralSpace) - w
  have hz : z ∈ integrandSpace H hH0 hH1 := (integrandSpace H hH0 hH1).sub_mem v.property w.property
  have hk : integrandSpace H hH0 hH1 ≤ (innerSL ℝ z).ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro x ⟨t, rfl⟩
      change inner ℝ z (normalized H hH0 hH1 t) = 0
      have ht := congrFun he t
      change inner ℝ (v : SpectralSpace) _ = inner ℝ (w : SpectralSpace) _ at ht
      simp only [z, inner_sub_left, ht, sub_self]
    · exact (innerSL ℝ z).isClosed_ker
  have hi : inner ℝ z z = 0 := hk hz
  have hzero : z = 0 := inner_self_eq_zero.mp hi
  exact Subtype.ext (sub_eq_zero.mp hzero)

def direction (t : ℝ≥0) : CoefficientSpace :=
  hilbertEmbedding SpectralSpace (normalized H hH0 hH1 t)

def value (t : ℝ≥0) : GaussianL2 := firstChaosEmbedding (direction H hH0 hH1 t)
def process (t : ℝ≥0) : SampleSpace → ℝ := value H hH0 hH1 t

theorem process_measurable (t : ℝ≥0) : Measurable (process H hH0 hH1 t) :=
  (Lp.stronglyMeasurable _).measurable

theorem process_isGaussianProcess : IsGaussianProcess (process H hH0 hH1) gaussianProduct :=
  firstChaos_isGaussianProcess.comp_right (direction H hH0 hH1)

theorem process_memLp (t : ℝ≥0) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (process H hH0 hH1 t) p gaussianProduct :=
  (firstChaos_hasGaussianLaw (direction H hH0 hH1 t)).memLp hp

theorem process_centered (t : ℝ≥0) : ∫ ω, process H hH0 hH1 t ω ∂gaussianProduct = 0 :=
  firstChaos_integral _

theorem process_covariance (s t : ℝ≥0) :
    cov[process H hH0 hH1 s, process H hH0 hH1 t; gaussianProduct] =
      ((s:ℝ)^(2*H) + (t:ℝ)^(2*H) - |(t:ℝ)-s|^(2*H)) / 2 := by
  rw [process, process, value, value, firstChaos_covariance]
  change inner ℝ (hilbertEmbedding SpectralSpace _) (hilbertEmbedding SpectralSpace _) = _
  rw [(hilbertEmbedding SpectralSpace).inner_map_map, normalized_inner]
  simp only [FractionalSpectralGeometry.covariance, abs_of_nonneg s.coe_nonneg, abs_of_nonneg t.coe_nonneg]

theorem process_law (t : ℝ≥0) :
    gaussianProduct.map (process H hH0 hH1 t) =
      gaussianReal 0 ⟨(t:ℝ)^(2*H), Real.rpow_nonneg t.coe_nonneg _⟩ := by
  rw [process, value, firstChaos_law]
  simp only [direction, (hilbertEmbedding SpectralSpace).norm_map, normalized_norm_sq,
    abs_of_nonneg t.coe_nonneg]
  rfl

theorem value_zero : value H hH0 hH1 0 = 0 := by simp [value, direction, normalized_zero]

theorem value_increment_norm (s t : ℝ≥0) :
    ‖value H hH0 hH1 t - value H hH0 hH1 s‖ = |(t:ℝ)-s|^H := by
  rw [value, value, ← map_sub, firstChaosEmbedding.norm_map]
  change ‖hilbertEmbedding SpectralSpace _ - hilbertEmbedding SpectralSpace _‖ = _
  rw [← map_sub, (hilbertEmbedding SpectralSpace).norm_map, normalized_sub_norm]

theorem increment_sq_integrable (s t : ℝ≥0) :
    Integrable (fun ω => (process H hH0 hH1 t ω - process H hH0 hH1 s ω)^2) gaussianProduct :=
  ((process_memLp H hH0 hH1 t 2 (by simp)).sub
    (process_memLp H hH0 hH1 s 2 (by simp))).integrable_sq

theorem increment_secondMoment (s t : ℝ≥0) :
    ∫ ω, (process H hH0 hH1 t ω - process H hH0 hH1 s ω)^2 ∂gaussianProduct =
      |(t:ℝ)-s|^(2*H) := by
  have hn : ‖value H hH0 hH1 t - value H hH0 hH1 s‖^2 = |(t:ℝ)-s|^(2*H) := by
    rw [value_increment_norm, ← Real.rpow_mul_natCast (abs_nonneg _)]
    congr 1
    ring
  rw [← hn, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (value H hH0 hH1 t) (value H hH0 hH1 s)] with ω he
  simp only [Pi.sub_apply] at he
  change (value H hH0 hH1 t ω - value H hH0 hH1 s ω)^2 =
    inner ℝ ((value H hH0 hH1 t - value H hH0 hH1 s) ω)
      ((value H hH0 hH1 t - value H hH0 hH1 s) ω)
  rw [he, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem value_derivative_graph (t : ℝ≥0) :
    (value H hH0 hH1 t, scalarTensor (direction H hH0 hH1 t) gaussianOne) ∈
      closedCylindricalDerivative.graph := by
  have hg := closedCylindricalDerivative_core_graph (firstChaosPolynomial (direction H hH0 hH1 t))
  have hf : (firstChaosPolynomial (direction H hH0 hH1 t) : GaussianL2) = value H hH0 hH1 t :=
    Lp.ext (firstChaosPolynomial_coeFn _)
  have hd : polynomialDerivative (firstChaosPolynomial (direction H hH0 hH1 t)) =
      scalarTensor (direction H hH0 hH1 t) gaussianOne := by
    apply Lp.ext
    filter_upwards [firstChaosPolynomial_derivative_coeFn (direction H hH0 hH1 t),
      scalarTensor_coeFn (direction H hH0 hH1 t) gaussianOne, gaussianOne_coeFn] with ω hd ht ho
    rw [hd, ht, ho, one_smul]
  rwa [hf, hd] at hg

end OperatorDerivativeRewrite.Foundation.FractionalGaussianProcess
