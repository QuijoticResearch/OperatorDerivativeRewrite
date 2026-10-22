import Foundation.IBMCovarianceVariationControl
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral

/-! Literal signed predictable integrals agree with ACTUAL mixed stochastic sums. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFiniteSignedCovarianceIntegral
open IBMTimeAveragedObservable IBMPredictableRectangles IBMPredictableFiniteIntegral
open IBMPredictableCovarianceMeasure IBMMixedPredictableEnergy IBMCovarianceVariationControl
local instance : MeasurableSpace Space := IBMNaturalFiltrationObstruction.naturalFiltration.predictable
local instance (F G : JointL2) : IsFiniteMeasure (covariance F G).variation := finite_variation F G

theorem process_memLp_any (μ : Measure Space) [IsFiniteMeasure μ] (l : Index →₀ ℝ) :
    MemLp (processLinear l) 2 μ := by
  have he : processLinear l = fun p => ∑ d ∈ l.support, l d * basisProcess d p :=
    funext (processLinear_apply l)
  rw [he]
  apply memLp_finsetSum
  intro d hd
  have hb : MemLp (basisProcess d) 2 μ :=
    (memLp_const (1 : ℝ)).indicator (rect_predictable _ _ _ (event_measurable d))
  exact hb.const_mul (l d)

theorem product_signed_integrable (F G : JointL2) (l k : Index →₀ ℝ) :
    (covariance F G).Integrable (fun p => processLinear l p * processLinear k p) :=
  (process_memLp_any (covariance F G).variation l).integrable_mul
    (process_memLp_any (covariance F G).variation k)

def signedPairing (F G : JointL2) (l k : Index →₀ ℝ) : ℝ :=
  ∫ᵛ p, processLinear l p * processLinear k p ∂<•covariance F G

theorem basis_signed_integral (F G : JointL2) (d e : Index) :
    (∫ᵛ p, basisProcess d p * basisProcess e p ∂<•covariance F G) =
      covariance F G (rect (left d) (right d) (event d) ∩ rect (left e) (right e) (event e)) := by
  have hp : (fun p => basisProcess d p * basisProcess e p) =
      (rect (left d) (right d) (event d) ∩ rect (left e) (right e) (event e)).indicator
        (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hd : p ∈ rect (left d) (right d) (event d) <;>
      by_cases he : p ∈ rect (left e) (right e) (event e) <;> simp [basisProcess, hd, he]
  rw [hp]
  simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul, one_mul, mul_one] using
    (VectorMeasure.integral_indicator_const (μ := covariance F G)
      (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (1 : ℝ)
      ((rect_predictable (left d) (right d) (event d) (event_measurable d)).inter
        (rect_predictable (left e) (right e) (event e) (event_measurable e))))

theorem finite_signed_pairing (F G : JointL2) (l k : Index →₀ ℝ) :
    signedPairing F G l k = inner ℝ (integralLinear F l) (integralLinear G k) := by
  change (∫ᵛ p, processLinear l p * processLinear k p ∂<•covariance F G) = _
  induction l using Finsupp.induction_linear with
  | zero => simp
  | add l m hl hm =>
      simp only [map_add, Pi.add_apply, add_mul, inner_add_left]
      rw [VectorMeasure.integral_fun_add (product_signed_integrable F G l k)
        (product_signed_integrable F G m k), hl, hm]
  | single d a =>
      induction k using Finsupp.induction_linear with
      | zero => simp
      | add k m hk hm =>
          simp only [map_add, Pi.add_apply, mul_add, inner_add_right]
          rw [VectorMeasure.integral_fun_add (product_signed_integrable F G (Finsupp.single d a) k)
            (product_signed_integrable F G (Finsupp.single d a) m), hk, hm]
      | single e b =>
          simp only [integralLinear, processLinear, Finsupp.linearCombination_single,
            real_inner_smul_left, real_inner_smul_right, Pi.smul_apply, smul_eq_mul]
          simp_rw [mul_mul_mul_comm a _ b _]
          have hs : (∫ᵛ p, (a*b)*(basisProcess d p*basisProcess e p) ∂<•covariance F G) =
              (a*b)*(∫ᵛ p, basisProcess d p*basisProcess e p ∂<•covariance F G) := by
            simpa only [smul_eq_mul] using
              (VectorMeasure.integral_fun_smul (μ := covariance F G)
                (B := (ContinuousLinearMap.lsmul ℝ ℝ).flip) (a*b) (fun p => basisProcess d p*basisProcess e p))
          rw [hs, basis_signed_integral, basis_mixed_energy]
          ring

theorem signed_pairing_energy (F G : JointL2) (l k : Index →₀ ℝ) :
    signedPairing F G l k = mixedEnergy F G l k :=
  (finite_signed_pairing F G l k).trans (finite_mixed_energy F G l k)

end OperatorDerivativeRewrite.Foundation.IBMFiniteSignedCovarianceIntegral
