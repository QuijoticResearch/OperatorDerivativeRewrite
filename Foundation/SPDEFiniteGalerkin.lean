import Foundation.SPDEFiniteModes
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! Actual Euclidean-valued finite stochastic convolution at a fixed terminal time. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.SPDEFiniteGalerkin
open SPDEFiniteModes SPDEModulatedResponse
open GaussianTimeHilbert InfiniteGaussian GaussianHilbertProcess
attribute [local instance] timeHilbert_secondCountable

def responseField {n : ℕ} (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (M : Fin n → ℝ)
    (hM : ∀ i s, |g i s| ≤ M i) (c : Fin n → ℝ) :
    SampleSpace → EuclideanSpace ℝ (Fin n) :=
  fun ω => WithLp.toLp 2 (fun i => c i * modeResponse i α hα t (g i) (hg i) (M i) (hM i) ω)

theorem responseField_memLp {n : ℕ} (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (M : Fin n → ℝ)
    (hM : ∀ i s, |g i s| ≤ M i) (c : Fin n → ℝ) :
    MemLp (responseField α hα t g hg M hM c) 2 gaussianProduct := by
  rw [memLp_piLp_iff]
  intro i
  change MemLp (fun ω => c i * modeResponse i α hα t (g i) (hg i) (M i) (hM i) ω)
    2 gaussianProduct
  exact (Lp.memLp (modeResponse i α hα t (g i) (hg i) (M i) (hM i))).const_mul _

def responseL2 {n : ℕ} (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (M : Fin n → ℝ)
    (hM : ∀ i s, |g i s| ≤ M i) (c : Fin n → ℝ) :
    Lp (EuclideanSpace ℝ (Fin n)) 2 gaussianProduct :=
  (responseField_memLp α hα t g hg M hM c).toLp
    (responseField α hα t g hg M hM c)

theorem responseL2_coeFn {n : ℕ} (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (M : Fin n → ℝ)
    (hM : ∀ i s, |g i s| ≤ M i) (c : Fin n → ℝ) :
    responseL2 α hα t g hg M hM c =ᵐ[gaussianProduct]
      responseField α hα t g hg M hM c := MemLp.coeFn_toLp _

theorem responseL2_energy {n : ℕ} (α : ℝ) (hα : 1 / 2 < α)
    (t : ℝ≥0) (g : Fin n → ℝ → ℝ)
    (hg : ∀ i, Measurable (g i)) (M : Fin n → ℝ)
    (hM : ∀ i s, |g i s| ≤ M i) (c : Fin n → ℝ) :
    ‖responseL2 α hα t g hg M hM c‖ ^ 2 =
      ∑ i, (c i)^2 * ∫ s, (modulatedResponse α t (g i) s)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
  have hfield : (fun ω => inner ℝ
      (responseL2 α hα t g hg M hM c ω)
      (responseL2 α hα t g hg M hM c ω)) =ᵐ[gaussianProduct]
      fun ω => ∑ i, (c i * modeResponse i α hα t (g i) (hg i) (M i) (hM i) ω)^2 := by
    filter_upwards [responseL2_coeFn α hα t g hg M hM c] with ω hw
    rw [hw, real_inner_self_eq_norm_sq, EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [integral_congr_ae hfield]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    have hmode : (∫ ω, (modeResponse i α hα t (g i) (hg i) (M i) (hM i) ω)^2
        ∂gaussianProduct) =
        ‖modeResponse i α hα t (g i) (hg i) (M i) (hM i)‖^2 := by
      rw [← real_inner_self_eq_norm_sq, L2_inner_eq_integral]
      apply integral_congr_ae
      filter_upwards [] with ω
      simp [pow_two]
    rw [show (fun ω =>
        (c i * modeResponse i α hα t (g i) (hg i) (M i) (hM i) ω)^2) =
        fun ω => (c i)^2 *
          (modeResponse i α hα t (g i) (hg i) (M i) (hM i) ω)^2 by
          funext ω; ring,
      integral_const_mul, hmode,
      modeResponse_energy i α hα t (g i) (hg i) (M i) (hM i)]
  · intro i hi
    exact ((Lp.memLp (modeResponse i α hα t (g i) (hg i) (M i) (hM i))).const_mul
      (c i)).integrable_sq

end OperatorDerivativeRewrite.Foundation.SPDEFiniteGalerkin
