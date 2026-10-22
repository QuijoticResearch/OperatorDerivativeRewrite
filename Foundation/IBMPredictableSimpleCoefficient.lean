import Foundation.IBMPredictableCoefficientLift

/-! Exact finite realizations for raw-past simple coefficients and actual G steps. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPredictableSimpleCoefficient
open IBMPredictableRectangles IBMPredictableFiniteIntegral IBMPredictableRingContent
open IBMPredictableCoefficientLift IBMPredictableLpDictionary IBMTimeAveragedObservable
open IBMNaturalFiltrationObstruction IBMWeightedTerminalEnergy
open IBMIntrinsicMartingaleStep (Coefficient)
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace Space := naturalFiltration.predictable

theorem simple_lift_mem {s t : ℝ≥0} (hst : s ≤ t)
    (f : @SimpleFunc IBMSourceLaws.JointSample (naturalFiltration s) ℝ) :
    lift s t f ∈ processSpace := by
  classical
  let : MeasurableSpace IBMSourceLaws.JointSample := naturalFiltration s
  let d (c : ℝ) : Index := ⟨(s,t,f ⁻¹' {c}), hst, f.measurableSet_fiber c⟩
  have hm : (∑ c ∈ f.range, c • basisProcess (d c)) ∈ processSpace :=
    processSpace.sum_mem fun c _ => processSpace.smul_mem c (basis_mem (d c))
  have he : (∑ c ∈ f.range, c • basisProcess (d c)) = lift s t f := by
    funext p
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hr : p.1 ∈ Ioc s t
    · rw [Finset.sum_eq_single (f p.2)]
      · simp [basisProcess, d, left, right, event, rect, hr, lift]
      · intro c hc hne
        have hn : f p.2 ≠ c := Ne.symm hne
        simp [basisProcess, d, left, right, event, rect, hr, hn]
      · exact fun hn => (hn (f.mem_range_self p.2)).elim
    · rw [Finset.sum_eq_zero (fun c _ => by simp [basisProcess, d, left, right, event, rect, hr])]
      simp only [lift, indicator_of_notMem hr]
  exact he ▸ hm

theorem actual_finite_identification (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s) (l : Index →₀ ℝ) (he : processLinear l = lift s t a.function) :
    integralLinear F l = IBMGermPredictableStep.stepClass F s t a := by
  classical
  have hh := IBMFiniteIntervalIdentification.interval_equal_ae IBMSourceLaws.jointMeasure
    (fun d : l.support => left d.val) (fun d : l.support => right d.val)
    (fun d : l.support => fun ω => l d.val *
      (eventCoefficient (left d.val) (event d.val) (event_measurable d.val)).function ω)
    (fun _ : Unit => s) (fun _ : Unit => t) (fun _ : Unit => a.function)
    (fun d => ordered d.val) (fun _ => hst) (IBMObservedTerminalMartingale.channel F) (by
      intro r
      apply ae_of_all
      intro ω
      change (∑ d : l.support, (Ioc (left d.val) (right d.val)).indicator
        (fun _ => l d.val * (eventCoefficient (left d.val) (event d.val)
          (event_measurable d.val)).function ω) r) = _
      rw [show (∑ d : l.support, (Ioc (left d.val) (right d.val)).indicator
        (fun _ => l d.val * (eventCoefficient (left d.val) (event d.val)
          (event_measurable d.val)).function ω) r) =
        ∑ d ∈ l.support, (Ioc (left d) (right d)).indicator
          (fun _ => l d * (eventCoefficient (left d) (event d) (event_measurable d)).function ω) r
        from Finset.sum_coe_sort l.support (fun d => (Ioc (left d) (right d)).indicator
          (fun _ => l d * (eventCoefficient (left d) (event d) (event_measurable d)).function ω) r)]
      simp only [Fintype.sum_unique]
      have hp := congrFun he (r,ω)
      rw [processLinear_apply] at hp
      convert hp using 1
      · apply Finset.sum_congr rfl
        intro d _
        rw [basisProcess_formula]
        by_cases hr : r ∈ Ioc (left d) (right d) <;>
          simp [IBMIntrinsicPredictableProcess.timeStep, hr]
      · rfl)
  apply Lp.ext
  filter_upwards [integralLinear_ae F l, hh, IBMGermPredictableStep.stepClass_ae F hst a]
    with ω hi hc ha
  rw [hi, ha]
  have hs := Finset.sum_coe_sort l.support (fun d =>
    (l d * (eventCoefficient (left d) (event d) (event_measurable d)).function ω) *
      (IBMObservedTerminalMartingale.channel F (right d) ω -
        IBMObservedTerminalMartingale.channel F (left d) ω))
  exact hs.symm.trans (by simpa only [Fintype.sum_unique] using hc)

theorem simple_integral_identification (F : JointL2) {s t : ℝ≥0} (hst : s ≤ t)
    (a : Coefficient s)
    (f : @SimpleFunc IBMSourceLaws.JointSample (naturalFiltration s) ℝ)
    (ha : a.function = f) :
    IBMFullPredictableIntegral.integral F (coefficientLp F hst a) =
      IBMGermPredictableStep.stepClass F s t a := by
  obtain ⟨l, hl⟩ := simple_lift_mem hst f
  have hp : processLinear l = lift s t a.function := by rw [ha]; exact hl
  have hd : coefficientLp F hst a = dictionary F l := by
    apply Lp.ext
    exact (coefficientLp_ae F hst a).trans (hp ▸ (dictionary_ae F l)).symm
  rw [hd, IBMFullPredictableIntegral.integral_dictionary]
  exact actual_finite_identification F hst a l hp

end OperatorDerivativeRewrite.Foundation.IBMPredictableSimpleCoefficient
