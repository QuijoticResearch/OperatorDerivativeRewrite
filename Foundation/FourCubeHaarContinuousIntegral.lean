import Foundation.FourCubeThermalMixedDifference
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Continuous-linear integration on the actual compact finite-Haar state space. -/
noncomputable section
open MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarContinuousIntegral
open FourCubeHaarParity QuaternionSU2Representation SU2TraceHessianModel

abbrev Observables := C(InteriorState,ℝ)
abbrev Parameters := Fin 3 → ℝ

theorem observable_integrable (f : Observables) : Integrable f interiorHaar :=
  Integrable.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall (fun s => f.norm_coe_le_norm s))

def haarLinear : Observables →ₗ[ℝ] ℝ where
  toFun f := ∫ s, f s ∂interiorHaar
  map_add' f g := integral_add (observable_integrable f) (observable_integrable g)
  map_smul' r f := integral_smul r f

def haarIntegral : Observables →L[ℝ] ℝ := haarLinear.mkContinuous 1 (by
  intro f
  have hh := norm_integral_le_of_norm_le_const
    (μ := interiorHaar) (Filter.Eventually.of_forall (fun s => f.norm_coe_le_norm s))
  change ‖∫ s, f s ∂interiorHaar‖ ≤ 1*‖f‖
  simpa only [probReal_univ,mul_one,one_mul] using hh)

theorem haarIntegral_apply (f : Observables) : haarIntegral f=∫ s, f s ∂interiorHaar := rfl

theorem exp_apply (f : Observables) (s : InteriorState) :
    NormedSpace.exp f s=Real.exp (f s) := by
  have hh := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℚ ℝ s)
    (ContinuousMap.evalCLM ℝ s).continuous f
  simpa only [ContinuousMap.evalAlgHom_apply,Real.exp_eq_exp_ℝ] using hh

theorem exponential_contDiff : ContDiff ℝ ∞ (NormedSpace.exp : Observables → Observables) := by
  apply contDiff_iff_contDiffAt.mpr
  intro f
  exact (NormedSpace.exp_analytic (𝕂 := ℝ) f).contDiffAt

theorem integrated_exponential_contDiff (A : Parameters → Observables)
    (hA : ContDiff ℝ ∞ A) (β : ℝ) :
    ContDiff ℝ ∞ (fun a => haarIntegral (NormedSpace.exp ((-β) • A a))) :=
  haarIntegral.contDiff.comp (exponential_contDiff.comp (hA.const_smul (-β)))

def traceLinear : M2 →ₗ[ℝ] ℝ := (1/2 : ℝ) •
  (Complex.reLm.comp (Matrix.traceLinearMap (Fin 2) ℝ ℂ))

def traceContinuous : M2 →L[ℝ] ℝ := traceLinear.toContinuousLinearMap

theorem traceContinuous_apply (M : M2) : traceContinuous M=traceReal M/2 := by
  change (1/2 : ℝ)*(Matrix.trace M).re=(Matrix.trace M).re/2
  ring

def probeLinear (e : OneSidedBlockRank.Interior) : M2 →ₗ[ℝ] Observables where
  toFun M := ⟨fun s => traceContinuous (M*(s e : M2)),
    traceContinuous.continuous.comp
      (continuous_const.mul (continuous_subtype_val.comp (continuous_apply e)))⟩
  map_add' M N := by
    ext s
    change traceContinuous ((M+N)*(s e : M2))=_
    rw [Matrix.add_mul,map_add]
    rfl
  map_smul' r M := by
    ext s
    change traceContinuous ((r • M)*(s e : M2))=_
    rw [Matrix.smul_mul,map_smul]
    rfl

def probe (e : OneSidedBlockRank.Interior) : M2 →L[ℝ] Observables :=
  (probeLinear e).toContinuousLinearMap

theorem probe_apply (e : OneSidedBlockRank.Interior) (M : M2) (s : InteriorState) :
    probe e M s=traceReal (M*(s e : M2))/2 := by
  change traceContinuous (M*(s e : M2))=_
  exact traceContinuous_apply _

end OperatorDerivativeRewrite.Foundation.FourCubeHaarContinuousIntegral
