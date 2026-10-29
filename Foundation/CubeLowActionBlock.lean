import Foundation.CubeAxialGauge
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Genuine positive-Haar low-action blocks for the actual Wilson slab.
Constants may depend on the block threshold; no volume-uniform estimate is asserted. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeLowActionBlock
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab

private instance su2_secondCountable : SecondCountableTopology SU2 := by
  letI : SecondCountableTopology (Quaternion ℝ) :=
    Quaternion.linearIsometryEquivTuple.toHomeomorph.secondCountableTopology
  exact QuaternionSU2Representation.homeomorph.symm.secondCountableTopology
private instance state_borel : BorelSpace State := by infer_instance
private instance gauge_borel : BorelSpace Gauge := by infer_instance
private instance boundary_open : boundaryHaar.IsOpenPosMeasure := by unfold boundaryHaar; infer_instance
private instance gauge_open : gaugeHaar.IsOpenPosMeasure := by unfold gaugeHaar; infer_instance

private theorem trace_continuous : Continuous halfTrace := by
  have he : halfTrace = fun A : SU2 => ((A : SU2TraceHessianModel.M2) 0 0).re/2+
      ((A : SU2TraceHessianModel.M2) 1 1).re/2 := by
    funext A
    simp [halfTrace,SU2TraceHessianModel.traceReal,Matrix.trace_fin_two,add_div]
  rw [he]
  have hentry (i j : Fin 2) : Continuous (fun A : SU2 => (A : SU2TraceHessianModel.M2) i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
  exact ((Complex.continuous_re.comp (hentry 0 0)).div_const 2).add
    ((Complex.continuous_re.comp (hentry 1 1)).div_const 2)

private theorem spatial_continuous : Continuous spatialAction := by
  unfold spatialAction
  apply continuous_finsetSum
  intro p _
  exact continuous_const.sub (trace_continuous.comp (by unfold spatialWord; fun_prop))

private theorem temporal_continuous :
    Continuous (fun q : (State × State) × Gauge => temporalAction q.1.1 q.1.2 q.2) := by
  unfold temporalAction
  apply continuous_finsetSum
  intro e _
  exact continuous_const.sub (trace_continuous.comp (by unfold temporalWord; fun_prop))

theorem action_continuous :
    Continuous (fun q : (State × State) × Gauge => halfAction q.1.1 q.1.2 q.2) := by
  unfold halfAction
  exact (((spatial_continuous.comp (continuous_fst.comp continuous_fst)).div_const 2).add
    temporal_continuous).add
      ((spatial_continuous.comp (continuous_snd.comp continuous_fst)).div_const 2)

private theorem action_one : halfAction (1 : State) 1 1=0 := by
  have hs : spatialAction (1 : State)=0 := by
    unfold spatialAction
    apply Finset.sum_eq_zero
    intro p _
    simp [spatialWord,SU2OpenLinkGaugeObstruction.halfTrace_one]
  have ht : temporalAction (1 : State) 1 1=0 := by
    unfold temporalAction
    apply Finset.sum_eq_zero
    intro e _
    simp [temporalWord,SU2OpenLinkGaugeObstruction.halfTrace_one]
  rw [halfAction,hs,ht]
  norm_num

attribute [local irreducible] halfAction spatialAction temporalAction

private theorem small_rectangle (eta : ℝ) (he : 0 < eta) :
    ∃ B : Set State, ∃ D : Set Gauge, IsOpen B ∧ (1 : State) ∈ B ∧
      IsOpen D ∧ (1 : Gauge) ∈ D ∧
      ∀ U ∈ B, ∀ V ∈ B, ∀ a ∈ D, halfAction U V a ≤ eta := by
  let S : Set ((State × State) × Gauge) := {q | halfAction q.1.1 q.1.2 q.2 < eta}
  have hS : IsOpen S := isOpen_lt action_continuous continuous_const
  have h1 : (((1 : State),1),(1 : Gauge)) ∈ S := by
    change halfAction (1 : State) 1 1 < eta
    rw [action_one]
    exact he
  obtain ⟨E,D,hE,hED,hD,h1D,hsub⟩ := mem_nhds_prod_iff'.mp (hS.mem_nhds h1)
  obtain ⟨B1,B2,hB1,h1B1,hB2,h1B2,hBB⟩ := mem_nhds_prod_iff'.mp (hE.mem_nhds hED)
  refine ⟨B1 ∩ B2,D,hB1.inter hB2,⟨h1B1,h1B2⟩,hD,h1D,?_⟩
  intro U hU V hV a ha
  have hs : ((U,V),a) ∈ S := hsub ⟨hBB ⟨hU.1,hV.2⟩,ha⟩
  change halfAction U V a < eta at hs
  exact hs.le

attribute [local irreducible] weight boundaryHaar gaugeHaar

theorem kernel_spatial_upper (beta : ℝ) (hb : 0 ≤ beta) (U V : State) :
    kernel beta U V ≤ Real.exp (-beta*spatialAction U/2) := by
  have hw (a : Gauge) : weight beta U V a ≤ Real.exp (-beta*spatialAction U/2) := by
    rw [weight]
    apply Real.exp_le_exp.mpr
    have ht := (temporal_action_bounds U V a).1
    have hv := (spatial_action_bounds V).1
    unfold halfAction
    nlinarith [mul_nonneg hb ht,mul_nonneg hb hv]
  unfold kernel
  simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono (weight_integrable beta U V) (integrable_const _) hw

/-- A real positive-Haar block for every action budget, uniform in nonnegative beta. -/
theorem positive_block (eta : ℝ) (he : 0 < eta) :
    ∃ B : Set State, ∃ k : ℝ, MeasurableSet B ∧ 0 < boundaryHaar.real B ∧ 0 < k ∧
      ∀ beta : ℝ, 0 ≤ beta → ∀ U ∈ B, ∀ V ∈ B,
        k*Real.exp (-beta*eta) ≤ kernel beta U V := by
  obtain ⟨B,D,hB,h1B,hD,h1D,hH⟩ := small_rectangle eta he
  have hbp : 0 < boundaryHaar.real B := by
    exact ENNReal.toReal_pos (IsOpen.measure_pos boundaryHaar hB ⟨1,h1B⟩).ne'
      (measure_lt_top _ _).ne
  have hdp : 0 < gaugeHaar.real D := by
    exact ENNReal.toReal_pos (IsOpen.measure_pos gaugeHaar hD ⟨1,h1D⟩).ne'
      (measure_lt_top _ _).ne
  refine ⟨B,gaugeHaar.real D,hB.measurableSet,hbp,hdp,?_⟩
  intro beta hb U hU V hV
  have hi := weight_integrable beta U V
  have hlow : (∫ a in D, Real.exp (-beta*eta) ∂gaugeHaar) ≤
      ∫ a in D, weight beta U V a ∂gaugeHaar := by
    apply setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn hD.measurableSet
    intro a ha
    rw [weight]
    exact Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left (hH U hU V hV a ha) hb])
  have hrest : (∫ a in D, weight beta U V a ∂gaugeHaar) ≤ kernel beta U V := by
    apply setIntegral_le_integral hi
    filter_upwards with a
    rw [weight]
    exact (Real.exp_pos _).le
  simpa only [setIntegral_const,smul_eq_mul] using hlow.trans hrest

end OperatorDerivativeRewrite.Foundation.CubeLowActionBlock
