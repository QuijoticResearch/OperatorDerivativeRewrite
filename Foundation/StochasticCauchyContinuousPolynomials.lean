import Foundation.StochasticCauchyPolynomialSums
import Foundation.StochasticCauchyBrownianRealization

/-! Transfer of the original native polynomial calculus to the existing
continuous circular Brownian paths. Fixed-time AE modification equality is
used explicitly; no equality of raw natural filtrations is asserted. -/
noncomputable section
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyContinuousPolynomials
open InfiniteGaussian ProductL2Curry ComplexL2Isometry IBMSourceLaws
open StochasticCauchyParameterizedObstruction StochasticCauchyJointPastIntegral
open StochasticCauchyComplexChannels StochasticCauchyPhysicalInput StochasticCauchyExponentialInput
open StochasticCauchyPolynomialInput StochasticCauchyPolynomialPrediction
open StochasticCauchyPolynomialReconstruction GaussianBrownianQuadraticVariation
attribute [local instance] StochasticCauchyParameterizedObstruction.finiteL2Exponent
  StochasticCauchyJointPastIntegral.input_complete StochasticCauchyJointPastIntegral.swapped_complete
  StochasticCauchyComplexChannels.complexInput_complete

/-- The existing continuous process is a modification of the exact source
representatives used by the original stochastic operators. -/
theorem continuous_value_ae (t : ℝ≥0) :
    StochasticCauchyBrownianRealization.value t =ᵐ[gaussianProduct.prod gaussianProduct] position t := by
  filter_upwards [
    (measurePreserving_fst (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (IBMConstructedSources.clockPath_coordinate_ae t),
    (measurePreserving_snd (μ := gaussianProduct) (ν := gaussianProduct)).quasiMeasurePreserving.ae_eq_comp
      (IBMConstructedSources.clockPath_coordinate_ae t)] with w hx hy
  simp only [Function.comp_apply] at hx hy
  rw [StochasticCauchyBrownianRealization.value_eq,hx,hy]
  rfl

theorem continuous_polynomial_ae (T : ℝ≥0) (p : Polynomial ℂ) :
    polynomialClass T p =ᵐ[gaussianProduct.prod gaussianProduct]
      fun w => p.eval (StochasticCauchyBrownianRealization.value T w) := by
  filter_upwards [polynomialClass_ae T p,continuous_value_ae T] with w hp hz
  rw [hp,hz]

/-- Genuine measurable continuous-path coefficients, on the original probability space. -/
theorem coefficient_jointly_measurable (p : Polynomial ℂ) :
    Measurable (fun q : ℝ≥0 × JointSample =>
      p.derivative.eval (StochasticCauchyBrownianRealization.value q.1 q.2)) := by
  have hc : Continuous (fun z : ℂ => p.derivative.eval z) := by fun_prop
  exact hc.measurable.comp StochasticCauchyBrownianRealization.value_jointly_measurable

theorem coefficient_path_continuous (p : Polynomial ℂ) (w : JointSample) :
    Continuous (fun t => p.derivative.eval (StochasticCauchyBrownianRealization.value t w)) := by
  have hc : Continuous (fun z : ℂ => p.derivative.eval z) := by fun_prop
  exact hc.comp (StochasticCauchyBrownianRealization.value_continuous w)

/-- Past measurability is AE with respect to the original raw joint past;
it is not a relabeling of that sigma algebra as the continuous natural past. -/
theorem continuous_polynomial_past (T : ℝ≥0) (p : Polynomial ℂ) :
    AEStronglyMeasurable[StochasticCauchyPastReconstruction.jointPast T]
      (fun w => p.eval (StochasticCauchyBrownianRealization.value T w))
      (gaussianProduct.prod gaussianProduct) := by
  have hc : Continuous (fun z : ℂ => p.eval z) := by fun_prop
  apply (hc.comp_stronglyMeasurable (position_stronglyMeasurable T)).aestronglyMeasurable.congr
  exact (continuous_value_ae T).symm.mono (fun w hw => congrArg (fun z => p.eval z) hw)

attribute [local instance] StochasticCauchyParameterizedObstruction.predictableTime

/-- The SAME original native stochastic integral, now on genuine continuous paths. -/
theorem native_reconstruction_ae (T : ℝ≥0) (p : Polynomial ℂ) :
    channel T false (StochasticCauchyPolynomialInput.normalizedInput T p)
      =ᵐ[gaussianProduct.prod gaussianProduct] fun w =>
        p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0 := by
  filter_upwards [polynomial_reconstruction_ae T p,continuous_value_ae T] with w hi hz
  rw [hi,hz]

/-- Physical coefficients of the original CANONICAL adjoint, on the continuous
process, with the exact AE-time then AE-source quantifier order. -/
theorem canonical_slices (T : ℝ≥0) (p : Polynomial ℂ) :
    ∀ᵐ r ∂timeLaw T, ∀ᵐ w : SampleSpace × SampleSpace ∂gaussianProduct.prod gaussianProduct,
      (fieldEmbedding T (realInput T (channelAdjoint T false (polynomialClass T p))) ((r,w.1),w.2):ℂ)+
      Complex.I*(fieldEmbedding T (imagInput T (channelAdjoint T false (polynomialClass T p))) ((r,w.1),w.2):ℂ) =
        (Real.sqrt 2:ℂ)*p.derivative.eval (StochasticCauchyBrownianRealization.value r.toNNReal w) := by
  filter_upwards [StochasticCauchyPolynomialReconstruction.canonical_slices T p] with r hr
  filter_upwards [hr,continuous_value_ae r.toNNReal] with w hi hz
  rw [hi,hz]

/-- Explicit sums built directly from the already constructed continuous paths. -/
def riemannSum (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) (w : JointSample) : ℂ :=
  ∑ i : Fin (N+1), p.derivative.eval (StochasticCauchyBrownianRealization.value
      (uniformTime T N i.castSucc) w)*
    (StochasticCauchyBrownianRealization.value (uniformTime T N i.succ) w-
      StochasticCauchyBrownianRealization.value (uniformTime T N i.castSucc) w)

theorem riemannSum_ae (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    riemannSum T p N =ᵐ[gaussianProduct.prod gaussianProduct]
      StochasticCauchyPolynomialSums.riemannSum T p N := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin (N+1) => continuous_value_ae (uniformTime T N i.castSucc)),
    ae_all_iff.mpr (fun i : Fin (N+1) => continuous_value_ae (uniformTime T N i.succ))] with w hl hr
  unfold riemannSum StochasticCauchyPolynomialSums.riemannSum
  exact Finset.sum_congr rfl (fun i _ => by rw [hl i,hr i])

theorem chronological_ae (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    channel T false (StochasticCauchyPolynomialInput.normalizedSteps T p N)
      =ᵐ[gaussianProduct.prod gaussianProduct] riemannSum T p N :=
  (StochasticCauchyPolynomialSums.chronological_ae T p N).trans (riemannSum_ae T p N).symm

theorem riemannSum_memLp (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    MemLp (riemannSum T p N) 2 (gaussianProduct.prod gaussianProduct) :=
  (StochasticCauchyPolynomialSums.riemannSum_memLp T p N).ae_eq (riemannSum_ae T p N).symm

theorem squared_error_integrable (T : ℝ≥0) (p : Polynomial ℂ) (N : ℕ) :
    Integrable (fun w => ‖riemannSum T p N w-
      (p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0)‖^2)
      (gaussianProduct.prod gaussianProduct) := by
  apply (StochasticCauchyPolynomialSums.squared_error_integrable T p N).congr
  filter_upwards [riemannSum_ae T p N,continuous_value_ae T] with w hs hz
  rw [hs,hz]

/-- Actual continuous-path sums converge in mean square. The whole sequence
is not asserted to converge almost surely, and no random horizon is used. -/
theorem mean_square_reconstruction (T : ℝ≥0) (p : Polynomial ℂ) :
    Tendsto (fun N => ∫ w,‖riemannSum T p N w-
      (p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0)‖^2
        ∂gaussianProduct.prod gaussianProduct) atTop (𝓝 0) := by
  have he (N : ℕ) : (∫ w,‖riemannSum T p N w-
      (p.eval (StochasticCauchyBrownianRealization.value T w)-p.eval 0)‖^2
      ∂gaussianProduct.prod gaussianProduct) =
      ∫ w,‖StochasticCauchyPolynomialSums.riemannSum T p N w-
        (p.eval (position T w)-p.eval 0)‖^2 ∂gaussianProduct.prod gaussianProduct := by
    apply integral_congr_ae
    filter_upwards [riemannSum_ae T p N,continuous_value_ae T] with w hs hz
    rw [hs,hz]
  simp_rw [he]
  exact StochasticCauchyPolynomialSums.mean_square_reconstruction T p

end OperatorDerivativeRewrite.Foundation.StochasticCauchyContinuousPolynomials
