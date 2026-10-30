import Foundation.CubeLocalKernel
import Foundation.SU2FourCurveJetTransfer
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Smooth rays of the actual homogeneous slab, retaining its free temporal root. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeChartAction
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeTemporalSlab CubeWilsonSlab CubeAxialSlice CubeAxialGauge CubeTemporalRootHaar
open CubeRelativeChart SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2FourCurveJetTransfer
attribute [local irreducible] CubeWilsonSlab.kernel law relativeHaar gaugeHaar

abbrev Boundary := Fin 5 → Triple

def chords (X : Boundary) (t : ℝ) : Chords := fun i => hemisphereChart (t • X i)
def boundaryRay (X : Boundary) (t : ℝ) : State := axialState (chords X t)
def temporalRay (c : SU2) (Z : CubeRelativeChart.Field) (t : ℝ) : Gauge :=
  assemble c (chartField (t • Z))
def actionRay (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (t : ℝ) : ℝ :=
  halfAction (boundaryRay X t) (boundaryRay Y t) (temporalRay c Z t)

attribute [local irreducible] boundaryRay temporalRay chords

theorem rooted_axial (q : Chords) (v : SpatialVertex) : rootedGauge (axialState q) v=1 := by
  change (if v 0=1 then axialState q ⟨(![0,0,0],0),rfl⟩ else 1)*
    (if v 1=1 then axialState q ⟨(![v 0,0,0],1),rfl⟩ else 1)*
    (if v 2=1 then axialState q ⟨(![v 0,v 1,0],2),rfl⟩ else 1)=1
  simp [axialState,chordLabel]

theorem reduced_axial (q : Chords) : reduced (axialState q)=q := by
  funext i
  unfold reduced gaugeAction
  rw [rooted_axial,rooted_axial,axial_chord]
  group

theorem chart_zero : hemisphereChart (0 : Triple)=1 := by
  apply Subtype.ext
  change (hemisphereChart (0 : Triple) : M2)=(1 : M2)
  simpa only [SU2HemisphereJets.curve,zero_smul] using SU2HemisphereJets.curve_zero (0 : Triple)

private theorem weight_contDiff (y : Triple) : ContDiff ℝ 2 (SU2HemisphereJets.weight y) := by
  have hp (t : ℝ) : 0<1+t^2*SU2HemisphereJets.sizeSq y := by
    have h := SU2HemisphereJets.sizeSq_nonneg y
    positivity
  have hb : ContDiff ℝ 2 (fun t : ℝ => 1+t^2*SU2HemisphereJets.sizeSq y) :=
    contDiff_const.add ((contDiff_id.pow 2).mul contDiff_const)
  exact (hb.sqrt (fun t => (hp t).ne')).inv (fun t => (Real.sqrt_pos.mpr (hp t)).ne')

theorem curve_contDiff (y : Triple) : ContDiff ℝ 2 (SU2HemisphereJets.curve y) := by
  have ha : ContDiff ℝ 2 (SU2HemisphereJets.affine y) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  convert! (weight_contDiff y).smul ha using 1
  funext t
  exact SU2HemisphereJets.curve_formula y t

theorem boundary_contDiff (X : Boundary) (e : SpatialEdge) :
    ContDiff ℝ 2 (fun t : ℝ => (boundaryRay X t e : M2)) := by
  unfold boundaryRay axialState chords
  cases he : chordLabel e with
  | none => simp only [Option.elim_none]; exact contDiff_const
  | some i => exact curve_contDiff (X i)

theorem temporal_contDiff (c : SU2) (Z : CubeRelativeChart.Field) (v : SpatialVertex) :
    ContDiff ℝ 2 (fun t : ℝ => (temporalRay c Z t v : M2)) := by
  unfold temporalRay assemble anchored chartField
  split_ifs with hv
  · exact contDiff_const
  · exact (curve_contDiff (Z ⟨v,hv⟩)).mul contDiff_const

theorem spatial_contDiff (X : Boundary) :
    ContDiff ℝ 2 (fun t : ℝ => spatialAction (boundaryRay X t)) := by
  unfold spatialAction
  apply ContDiff.sum
  intro p _
  have hp : ContDiff ℝ 2 (fun t : ℝ => fun i : Fin 4 => (boundaryRay X t (faceEdge p i) : M2)) :=
    contDiff_pi.mpr (fun i => boundary_contDiff X (faceEdge p i))
  convert traceAction_contDiff.comp hp using 1
  funext t
  rfl

theorem temporal_action_contDiff (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    ContDiff ℝ 2 (fun t : ℝ => temporalAction (boundaryRay X t) (boundaryRay Y t) (temporalRay c Z t)) := by
  unfold temporalAction
  apply ContDiff.sum
  intro e _
  let P (t : ℝ) : WordField := ![(boundaryRay X t e : M2),
    (temporalRay c Z t (shift e.val.1 e.val.2) : M2),
    (boundaryRay Y t e : M2),(temporalRay c Z t e.val.1 : M2)]
  have hp : ContDiff ℝ 2 P := by
    apply contDiff_pi.mpr
    intro i
    fin_cases i
    · exact boundary_contDiff X e
    · exact temporal_contDiff c Z _
    · exact boundary_contDiff Y e
    · exact temporal_contDiff c Z _
  convert traceAction_contDiff.comp hp using 1
  funext t
  rfl

theorem action_contDiff (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    ContDiff ℝ 2 (actionRay X Y c Z) :=
  ((spatial_contDiff X).div_const 2 |>.add (temporal_action_contDiff X Y c Z)).add
    ((spatial_contDiff Y).div_const 2)

theorem boundary_zero (X : Boundary) : boundaryRay X 0=1 := by
  funext e
  unfold boundaryRay axialState chords
  cases he : chordLabel e <;> simp [chart_zero]

theorem temporal_zero (c : SU2) (Z : CubeRelativeChart.Field) : temporalRay c Z 0=(fun _ => c) := by
  funext v
  simp [temporalRay,assemble,anchored,chartField,chart_zero]

theorem action_zero (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) : actionRay X Y c Z 0=0 := by
  simp [actionRay,boundary_zero,temporal_zero,halfAction,spatialAction,temporalAction,
    spatialWord,temporalWord,SU2OpenLinkGaugeObstruction.halfTrace_one]

theorem action_first_zero (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    deriv (actionRay X Y c Z) 0=0 := by
  have hm : IsLocalMin (actionRay X Y c Z) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [action_zero]
    exact (half_action_bounds _ _ _).1
  exact hm.deriv_eq_zero

def secondVariation (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) : ℝ :=
  deriv (deriv (actionRay X Y c Z)) 0

/-- The actual scalar Taylor limit; no identification with a different Hessian is used. -/
theorem action_quotient_limit (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    Tendsto (fun t : ℝ => actionRay X Y c Z t/t^2) (𝓝[≠] (0 : ℝ))
      (𝓝 (secondVariation X Y c Z/2)) := by
  let f := actionRay X Y c Z
  let q := secondVariation X Y c Z
  have hf : ContDiff ℝ 2 f := action_contDiff X Y c Z
  have h0 : f 0=0 := action_zero X Y c Z
  have h1 : deriv f 0=0 := action_first_zero X Y c Z
  have h2 : deriv (deriv f) 0=q := rfl
  have ht (t : ℝ) : taylorWithinEval f 2 Set.univ 0 t=(q/2)*t^2 := by
    simp [taylorWithinEval_succ,taylor_within_zero_eval,iteratedDerivWithin_univ,
      iteratedDeriv_succ,iteratedDeriv_zero,h0,h1,h2]
    ring
  have hr : (fun t : ℝ => f t-(q/2)*t^2) =o[𝓝 0] (fun t : ℝ => t^2) := by
    simpa only [ht,sub_zero] using taylor_isLittleO_univ (x₀ := 0) (n := 2) hf
  have h := ((hr.tendsto_div_nhds_zero.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 0)).add_const (q/2))
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hn : t≠0 := ht
  field_simp [hn]
  ring

end OperatorDerivativeRewrite.Foundation.CubeChartAction
