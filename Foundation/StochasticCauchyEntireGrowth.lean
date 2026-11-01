import Foundation.StochasticCauchyMeanResidual
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Entire polynomial-growth reduction with explicit global growth constants,
then actual native Brownian Cauchy realization. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyEntireGrowth

/-- Cauchy's estimate with an explicit polynomial growth bound forces every
higher Taylor derivative at the origin to vanish. -/
theorem high_derivative_zero (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ)
    (hg : ∀ z, ‖f z‖ ≤ C*(1+‖z‖)^N) (n : ℕ) (hn : N<n) :
    iteratedDeriv n f 0=0 := by
  let K : ℝ := (n.factorial:ℝ)*C*2^N
  have hK : 0 ≤ K := by dsimp [K]; positivity
  apply norm_le_zero_iff.mp
  apply le_of_forall_gt_imp_ge_of_dense
  intro ε hε
  let R : ℝ := max 1 (K/ε)
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hb : ∀ z ∈ sphere (0:ℂ) R, ‖f z‖ ≤ C*(1+R)^N := by
    intro z hz
    have hzR : ‖z‖=R := by simpa only [mem_sphere_iff_norm,sub_zero] using hz
    simpa only [hzR] using hg z
  have hnum : (n.factorial:ℝ)*(C*(1+R)^N) ≤ K*R^N := by
    have he : (1+R)^N ≤ (2*R)^N := by gcongr; linarith
    calc
      _ ≤ (n.factorial:ℝ)*(C*(2*R)^N) := by gcongr
      _ = _ := by dsimp only [K]; rw [mul_pow]; ring
  have hp : R^(N+1) ≤ R^n := pow_le_pow_right₀ hR1 (Nat.succ_le_of_lt hn)
  have hbound : ‖iteratedDeriv n f 0‖ ≤ K/R := by
    calc
      _ ≤ (n.factorial:ℝ)*(C*(1+R)^N)/R^n :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR hf.diffContOnCl hb
      _ ≤ (K*R^N)/R^n := div_le_div_of_nonneg_right hnum (pow_nonneg hR.le _)
      _ ≤ (K*R^N)/R^(N+1) := div_le_div_of_nonneg_left (mul_nonneg hK (pow_nonneg hR.le _)) (pow_pos hR _) hp
      _ = K/R := by rw [pow_succ]; field_simp
  refine hbound.trans ((div_le_iff₀ hR).mpr ?_)
  have he := (div_le_iff₀ hε).mp (le_max_right 1 (K/ε))
  nlinarith

def taylorPolynomial (f : ℂ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range (N+1), Polynomial.monomial n (iteratedDeriv n f 0/(n.factorial:ℂ))

/-- Entire functions of the stated growth are actual polynomials of degree at
most N. The local series and the global identity theorem are both checked. -/
theorem polynomial_of_growth (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hg : ∀ z, ‖f z‖ ≤ C*(1+‖z‖)^N) :
    (taylorPolynomial f N).natDegree ≤ N ∧ ∀ z,f z=(taylorPolynomial f N).eval z := by
  have hzero (n : ℕ) (hn : N<n) : iteratedDeriv n f 0/(n.factorial:ℂ)=0 := by
    rw [high_derivative_zero f hf C hC N hg n hn,zero_div]
  have hdeg : (taylorPolynomial f N).natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro n hn
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn)
  have hs := (hf.analyticAt 0).hasFPowerSeriesAt
  have he : f =ᶠ[𝓝 (0:ℂ)] fun z => (taylorPolynomial f N).eval z := by
    filter_upwards [hs.eventually_hasSum_sub] with z hz
    have hz' : HasSum (fun n => (iteratedDeriv n f 0/(n.factorial:ℂ))*z^n) (f z) := by
      simpa only [sub_zero,FormalMultilinearSeries.ofScalars_apply_eq,smul_eq_mul] using hz
    have hp : HasSum (fun n => (iteratedDeriv n f 0/(n.factorial:ℂ))*z^n)
        ((taylorPolynomial f N).eval z) := by
      unfold taylorPolynomial
      simp only [Polynomial.eval_finsetSum,Polynomial.eval_monomial]
      apply hasSum_sum_of_ne_finset_zero
      intro n hn
      have hn' : N<n := by
        have hh : ¬n<N+1 := by simpa only [Finset.mem_range] using hn
        omega
      rw [hzero n hn',zero_mul]
    exact hz'.unique hp
  have hall : f=(fun z => (taylorPolynomial f N).eval z) :=
    AnalyticOnNhd.eq_of_eventuallyEq (fun z _ => hf.analyticAt z)
      (fun z _ => (taylorPolynomial f N).differentiable.analyticAt z) he
  exact ⟨hdeg,fun z => congrFun hall z⟩

/-- The polynomial-growth class does not contain all entire functions. This
obstruction does not assert failure of reconstruction on other analytic domains. -/
theorem exponential_not_polynomial_growth :
    ¬∃ C : ℝ,0 ≤ C ∧ ∃ N : ℕ,∀ z : ℂ,‖Complex.exp z‖ ≤ C*(1+‖z‖)^N := by
  rintro ⟨C,hC,N,hg⟩
  have hz := high_derivative_zero Complex.exp Complex.differentiable_exp C hC N hg (N+1) (Nat.lt_succ_self N)
  have he : iteratedDeriv (N+1) Complex.exp 0=1 := by
    simpa using congrFun (iteratedDeriv_cexp_const_mul (N+1) 1) 0
  rw [he] at hz
  exact one_ne_zero hz

open InfiniteGaussian ProductL2Curry ComplexL2Isometry
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyPastReconstruction StochasticCauchyComplexChannels
open StochasticCauchyPolynomials StochasticCauchyMeanResidual
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
  StochasticCauchyParameterizedObstruction.predictableTime
  StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete GaussianTimeHilbert.timeHilbert_secondCountable

/-- A genuine observed terminal function and native plus integral, not just a
formal analytic target. Growth, domain, mean and every horizon are explicit. -/
theorem terminal_entire_realization (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (C : ℝ) (hC : 0 ≤ C) (N : ℕ) (hg : ∀ z, ‖f z‖ ≤ C*(1+‖z‖)^N) (T : ℝ≥0) :
    ∃ F : JointComplex,
      (F =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))) ∧
      MemLp (fun w : SampleSpace × SampleSpace =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))) 2 (gaussianProduct.prod gaussianProduct) ∧
      (cauchyProjection T false F =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-
          ∫ x,f ((GaussianTimeProcess.process T x.1:ℂ)+Complex.I*(GaussianTimeProcess.process T x.2:ℂ)) ∂gaussianProduct.prod gaussianProduct) ∧
      cauchyProjection T true F=0 ∧
      ∃ u : ComplexInput T, channel T false u =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        f ((GaussianTimeProcess.process T w.1:ℂ)+Complex.I*(GaussianTimeProcess.process T w.2:ℂ))-
          ∫ x,f ((GaussianTimeProcess.process T x.1:ℂ)+Complex.I*(GaussianTimeProcess.process T x.2:ℂ)) ∂gaussianProduct.prod gaussianProduct := by
  let p := taylorPolynomial f N
  have hp : ∀ z,f z=p.eval z := (polynomial_of_growth f hf C hC N hg).2
  let h := SeparableHilbertEmbedding.hilbertEmbedding GaussianTimeHilbert.TimeHilbert
    (GaussianTimeHilbert.timeVector T)
  have he : firstChaosEmbedding h=GaussianTimeProcess.wienerL2 T := rfl
  refine ⟨polynomialValue h p,?_,?_,?_,(terminal_raw_projections T p).2,?_⟩
  · simpa only [← hp,he,GaussianTimeProcess.process] using polynomial_value_ae h p
  · simpa only [← hp,he,GaussianTimeProcess.process] using polynomial_memLp h p
  · simpa only [← hp] using terminal_raw_cauchy_ae T p
  · simpa only [← hp] using terminal_polynomial_reconstruction T p

end OperatorDerivativeRewrite.Foundation.StochasticCauchyEntireGrowth
