import Foundation.StochasticCauchyEntireGrowth
import Mathlib.Analysis.Asymptotics.Basic
import Mathlib.Analysis.Normed.Group.Bounded

/-! Polynomial growth on the complex cocompact filter: compact exceptional sets
are controlled by continuity, without increasing the growth degree. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyAsymptoticGrowth
open StochasticCauchyEntireGrowth

theorem global_growth_of_compact (f : ℂ → ℂ) (hf : Continuous f)
    (K : Set ℂ) (hK : IsCompact K) (C : ℝ) (N : ℕ)
    (hg : ∀ z,z ∉ K → ‖f z‖ ≤ C*(1+‖z‖)^N) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ z,‖f z‖ ≤ D*(1+‖z‖)^N := by
  obtain ⟨M,hM⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  let D : ℝ := max 0 (max C M)
  have hD : 0 ≤ D := le_max_left _ _
  have hCD : C ≤ D := (le_max_left C M).trans (le_max_right _ _)
  have hMD : M ≤ D := (le_max_right C M).trans (le_max_right _ _)
  refine ⟨D,hD,fun z => ?_⟩
  by_cases hz : z ∈ K
  · exact (hM z hz).trans (hMD.trans (le_mul_of_one_le_right hD
      (one_le_pow₀ (by linarith [norm_nonneg z]))))
  · exact (hg z hz).trans (mul_le_mul_of_nonneg_right hCD (by positivity))

/-- Uniform polynomial growth at COMPLEX infinity, not along just one ray. -/
theorem global_growth_of_isBigO (f : ℂ → ℂ) (hf : Continuous f) (N : ℕ)
    (hg : f =O[cocompact ℂ] (fun z : ℂ => z^N)) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ z,‖f z‖ ≤ D*(1+‖z‖)^N := by
  obtain ⟨C,hC,hg⟩ := hg.exists_nonneg
  obtain ⟨K,hK,hB⟩ := mem_cocompact.mp hg.bound
  apply global_growth_of_compact f hf K hK C N
  intro z hz
  have hb := hB hz
  simp only [norm_pow] at hb
  refine hb.trans ?_
  gcongr <;> linarith [norm_nonneg z]

theorem polynomial_of_isBigO (f : ℂ → ℂ) (hf : Differentiable ℂ f) (N : ℕ)
    (hg : f =O[cocompact ℂ] (fun z : ℂ => z^N)) :
    (taylorPolynomial f N).natDegree ≤ N ∧ ∀ z,f z=(taylorPolynomial f N).eval z := by
  obtain ⟨D,hD,hg⟩ := global_growth_of_isBigO f hf.continuous N hg
  exact polynomial_of_growth f hf D hD N hg

theorem exponential_not_isBigO (N : ℕ) :
    ¬Complex.exp =O[cocompact ℂ] (fun z : ℂ => z^N) := by
  intro hg
  obtain ⟨D,hD,hg⟩ := global_growth_of_isBigO Complex.exp Complex.continuous_exp N hg
  exact exponential_not_polynomial_growth ⟨D,hD,N,hg⟩

open InfiniteGaussian StochasticCauchyParameterizedObstruction StochasticCauchyComplexChannels
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete

/-- The standard asymptotic growth convention yields the genuine native
Cauchy calculus, preserving the exact observed stochastic domains. -/
theorem terminal_asymptotic_realization (f : ℂ → ℂ) (hf : Differentiable ℂ f) (N : ℕ)
    (hg : f =O[cocompact ℂ] (fun z : ℂ => z^N)) (T : ℝ≥0) :
    ∃ F : JointComplex,
      (F =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))) ∧
      MemLp (fun w : SampleSpace × SampleSpace =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))) 2 (gaussianProduct.prod gaussianProduct) ∧
      (cauchyProjection T false F =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-
          ∫ x,f ((GaussianTimeProcess.process T x.1:ℂ)+Complex.I*(GaussianTimeProcess.process T x.2:ℂ)) ∂gaussianProduct.prod gaussianProduct) ∧
      cauchyProjection T true F=0 ∧
      ∃ u : ComplexInput T,channel T false u =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-
          ∫ x,f ((GaussianTimeProcess.process T x.1:ℂ)+Complex.I*(GaussianTimeProcess.process T x.2:ℂ)) ∂gaussianProduct.prod gaussianProduct := by
  obtain ⟨D,hD,hg⟩ := global_growth_of_isBigO f hf.continuous N hg
  exact terminal_entire_realization f hf D hD N hg T

end OperatorDerivativeRewrite.Foundation.StochasticCauchyAsymptoticGrowth
