import Foundation.IBMPredictableRectangles
import Mathlib.LinearAlgebra.Isomorphisms

/-! A finite actual stochastic integral on the space of eligible rectangle processes.
Only finite linear combinations are used; no continuum completion is declared. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableFiniteIntegral
open IBMPredictableRectangles IBMTimeAveragedObservable IBMObservedTerminalMartingale
open IBMWeightedTerminalEnergy IBMGermPredictableStep
set_option backward.isDefEq.respectTransparency false

abbrev Index := {d : ℝ≥0 × ℝ≥0 × Set IBMSourceLaws.JointSample //
  d.1 ≤ d.2.1 ∧ MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration d.1] d.2.2}

def left (d : Index) : ℝ≥0 := d.val.1
def right (d : Index) : ℝ≥0 := d.val.2.1
def event (d : Index) : Set IBMSourceLaws.JointSample := d.val.2.2

theorem ordered (d : Index) : left d ≤ right d := d.property.1
theorem event_measurable (d : Index) :
    MeasurableSet[IBMNaturalFiltrationObstruction.naturalFiltration (left d)] (event d) :=
  d.property.2

def basisProcess (d : Index) : Space → ℝ :=
  (rect (left d) (right d) (event d)).indicator (fun _ => 1)

def basisIntegral (F : JointL2) (d : Index) : JointL2 :=
  stepClass F (left d) (right d) (eventCoefficient (left d) (event d) (event_measurable d))

def processLinear : (Index →₀ ℝ) →ₗ[ℝ] (Space → ℝ) :=
  Finsupp.linearCombination ℝ basisProcess

def integralLinear (F : JointL2) : (Index →₀ ℝ) →ₗ[ℝ] JointL2 :=
  Finsupp.linearCombination ℝ (basisIntegral F)

theorem basisProcess_formula (d : Index) (r : ℝ≥0) (ω : IBMSourceLaws.JointSample) :
    basisProcess d (r,ω) = IBMIntrinsicPredictableProcess.timeStep (left d) (right d)
      (eventCoefficient (left d) (event d) (event_measurable d)) r ω := by
  by_cases hr : r ∈ Ioc (left d) (right d) <;> by_cases ha : ω ∈ event d <;>
    simp [basisProcess, rect, IBMIntrinsicPredictableProcess.timeStep,
      eventCoefficient, Set.indicator, hr, ha]

theorem processLinear_apply (l : Index →₀ ℝ) (p : Space) :
    processLinear l p = ∑ d ∈ l.support, l d * basisProcess d p := by
  simp only [processLinear, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem integralLinear_ae (F : JointL2) (l : Index →₀ ℝ) :
    integralLinear F l =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      ∑ d ∈ l.support, (l d * (eventCoefficient (left d) (event d)
        (event_measurable d)).function ω) * (channel F (right d) ω - channel F (left d) ω) := by
  have hc := (Finset.eventually_all l.support).mpr (fun d _ =>
    (Lp.coeFn_smul (l d) (basisIntegral F d)).and
      (stepClass_ae F (ordered d)
        (eventCoefficient (left d) (event d) (event_measurable d))))
  change (∑ d ∈ l.support, l d • basisIntegral F d) =ᵐ[IBMSourceLaws.jointMeasure] _
  filter_upwards [Lp.coeFn_finsetSum l.support (fun d => l d • basisIntegral F d), hc]
    with ω hs hcω
  rw [hs]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [(hcω d hd).1]
  simp only [Pi.smul_apply, smul_eq_mul]
  change l d * stepClass F (left d) (right d)
    (eventCoefficient (left d) (event d) (event_measurable d)) ω = _
  rw [(hcω d hd).2]
  ring

theorem kernel_inclusion (F : JointL2) :
    LinearMap.ker processLinear ≤ LinearMap.ker (integralLinear F) := by
  intro l hl
  change integralLinear F l = 0
  have he : processLinear l = 0 := hl
  apply Lp.ext
  filter_upwards [integralLinear_ae F l, Lp.coeFn_zero ℝ 2 IBMSourceLaws.jointMeasure] with ω hi hz
  rw [hi, hz]
  apply IBMFiniteIntervalIdentification.interval_relation l.support left right
    (fun d => l d * (eventCoefficient (left d) (event d) (event_measurable d)).function ω)
    (fun d _ => ordered d) (fun r => channel F r ω)
  intro r _
  have h := congrFun he (r,ω)
  rw [processLinear_apply] at h
  change (∑ d ∈ l.support, _) = 0 at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  rw [basisProcess_formula]
  by_cases hr : r ∈ Ioc (left d) (right d) <;>
    simp [IBMIntrinsicPredictableProcess.timeStep, Set.indicator, hr]

def processSpace : Submodule ℝ (Space → ℝ) := LinearMap.range processLinear

def integral (F : JointL2) : processSpace →ₗ[ℝ] JointL2 :=
  ((LinearMap.ker processLinear).liftQ (integralLinear F) (kernel_inclusion F)).comp
    processLinear.quotKerEquivRange.symm.toLinearMap

theorem integral_process (F : JointL2) (l : Index →₀ ℝ) :
    integral F ⟨processLinear l, ⟨l, rfl⟩⟩ = integralLinear F l := by
  change ((LinearMap.ker processLinear).liftQ (integralLinear F) (kernel_inclusion F))
    (processLinear.quotKerEquivRange.symm
      (⟨processLinear l, ⟨l, rfl⟩⟩ : LinearMap.range processLinear)) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

theorem basis_mem (d : Index) : basisProcess d ∈ processSpace := by
  refine ⟨Finsupp.single d 1, ?_⟩
  simp only [processLinear, Finsupp.linearCombination_single, one_smul]

theorem integral_basis (F : JointL2) (d : Index) :
    integral F ⟨basisProcess d, basis_mem d⟩ = basisIntegral F d := by
  have he := integral_process F (Finsupp.single d 1)
  simpa only [processLinear, integralLinear, Finsupp.linearCombination_single, one_smul] using he

theorem integral_support (F : JointL2) (H : processSpace) (A : Set IBMSourceLaws.JointSample)
    (hH : ∀ r ω, ω ∉ A → (H : Space → ℝ) (r, ω) = 0) :
    ∀ᵐ ω ∂IBMSourceLaws.jointMeasure, ω ∉ A → integral F H ω = 0 := by
  obtain ⟨l, hl⟩ := H.property
  have he : H = ⟨processLinear l, ⟨l, rfl⟩⟩ := Subtype.ext hl.symm
  rw [he, integral_process]
  filter_upwards [integralLinear_ae F l] with ω hi hn
  rw [hi]
  apply IBMFiniteIntervalIdentification.interval_relation l.support left right
    (fun d => l d * (eventCoefficient (left d) (event d) (event_measurable d)).function ω)
    (fun d _ => ordered d) (fun r => channel F r ω)
  intro r _
  have h := hH r ω hn
  rw [← hl, processLinear_apply] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro d _
  rw [basisProcess_formula]
  by_cases hr : r ∈ Ioc (left d) (right d) <;>
    simp [IBMIntrinsicPredictableProcess.timeStep, Set.indicator, hr]

end OperatorDerivativeRewrite.Foundation.IBMPredictableFiniteIntegral
