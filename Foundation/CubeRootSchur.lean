import Foundation.SU2RootAdjoint
import Foundation.CubeTemporalSchur

/-! Actual free-root mixed form in the verified temporal Schur geometry. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeRootSchur
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2FourWordVariation CubeTemporalSlab CubeAxialSlice CubeTemporalRootHaar
open CubeChartAction CubeMixedForm CubeSlabSecondVariation CubeTemporalSchur


def frameField (X : Boundary) : Fin 5 → Fin 3 → ℝ := fun i => SU2HemisphereJets.frame (X i)
def rotatedField (c : SU2) (Y : Boundary) : Fin 5 → Fin 3 → ℝ :=
  fun i => SU2HemisphereJets.frame (SU2RootAdjoint.rotate c (Y i))
def gaugeField (Z : CubeRelativeChart.Field) : GaugeVelocity :=
  fun v => if hv : v=root then 0 else SU2HemisphereJets.frame (Z ⟨v,hv⟩)

def difference (X Y : Boundary) (c : SU2) (a : Fin 3) : Fin 5 → ℝ :=
  fun j => frameField X j a-rotatedField c Y j a

def spatialCost (X : Boundary) : ℝ :=
  (∑ a : Fin 3,dotProduct (fun j => frameField X j a) (spatial.mulVec (fun j => frameField X j a)))/16

def effective (X Y : Boundary) (c : SU2) : ℝ :=
  spatialCost X+spatialCost Y+(∑ a : Fin 3,dotProduct (difference X Y c a)
    (kinetic.mulVec (difference X Y c a)))/8

def remainder (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) : ℝ :=
  (∑ a : Fin 3,dotProduct
    (grad.mulVec (anchor (gaugeField Z) a-responseMatrix.mulVec (difference X Y c a)))
    (grad.mulVec (anchor (gaugeField Z) a-responseMatrix.mulVec (difference X Y c a))))/8

private theorem edge_eq (X : Boundary) (e : SpatialEdge) :
    edgeVelocity X e=algebraElement (axialVelocity (frameField X) e) := by
  unfold edgeVelocity axialVelocity
  cases he : chordLabel e with
  | none => simp [algebraElement]
  | some i => rfl

private theorem vertex_eq (Z : CubeRelativeChart.Field) (v : SpatialVertex) :
    vertexVelocity Z v=algebraElement (gaugeField Z v) := by
  unfold vertexVelocity gaugeField
  split_ifs
  · simp [algebraElement]
  · rfl

private theorem rotated_edge_eq (c : SU2) (Y : Boundary) (e : SpatialEdge) :
    adjointVelocity c (edgeVelocity Y e)=algebraElement (axialVelocity (rotatedField c Y) e) := by
  unfold edgeVelocity axialVelocity
  cases he : chordLabel e with
  | none => simp [adjointVelocity,algebraElement]
  | some i => exact (SU2RootAdjoint.generator_rotate c (Y i)).symm

private theorem curl_eq (X : Boundary) (p : SpatialFace) :
    spatialCurl X p=algebraElement (curl (axialVelocity (frameField X)) p) := by
  unfold spatialCurl curl
  simp only [edge_eq,sub_eq_add_neg,algebraElement_add,algebraElement_neg]

private theorem mix_eq (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (e : SpatialEdge) :
    temporalMix X Y c Z e=algebraElement
      (axialVelocity (frameField X) e-axialVelocity (rotatedField c Y) e+gradient (gaugeField Z) e) := by
  unfold temporalMix gradient
  rw [rotated_edge_eq]
  simp only [edge_eq,vertex_eq,rotated_edge_eq,sub_eq_add_neg,algebraElement_add,algebraElement_neg]
  abel

private theorem trace_square (v : Fin 3 → ℝ) : traceReal ((algebraElement v)^2)= -lengthSq v/2 := by
  linarith [algebraElement_metric_sq v]

/-- Exact real-component identification of the ACTUAL root-dependent exponent. -/
theorem mixedForm_frames (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    mixedForm X Y c Z=spatialQuadratic (axialVelocity (frameField X))/16+
      spatialQuadratic (axialVelocity (frameField Y))/16+
      temporalQuadratic (axialVelocity (frameField X)) (axialVelocity (rotatedField c Y)) (gaugeField Z)/8 := by
  unfold mixedForm spatialQuadratic temporalQuadratic
  simp_rw [curl_eq,mix_eq,trace_square]
  simp only [Finset.sum_neg_distrib,← Finset.sum_div]
  ring

/-- Exact completion of all seven relative temporal directions for EVERY root c. -/
theorem completed_square (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    mixedForm X Y c Z=effective X Y c+remainder X Y c Z := by
  rw [mixedForm_frames,spatial_energy_actual,spatial_energy_actual,
    temporal_difference_actual,temporal_energy_actual]
  simp_rw [CubeTemporalSchur.completed_square]
  simp only [difference,Pi.sub_apply,Finset.sum_add_distrib]
  unfold effective spatialCost remainder difference
  ring

theorem effective_lower (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    effective X Y c ≤ mixedForm X Y c Z := by
  rw [completed_square]
  apply le_add_of_nonneg_right
  unfold remainder dotProduct
  exact div_nonneg (Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun i _ => mul_self_nonneg _))) (by norm_num)

private def unframe (v : Fin 3 → ℝ) : Triple := ![v 2/2,v 0/2,v 1/2]
private theorem frame_unframe (v : Fin 3 → ℝ) : SU2HemisphereJets.frame (unframe v)=v := by
  ext i
  fin_cases i <;> simp [SU2HemisphereJets.frame,unframe] <;> ring

/-- Explicit center in the actual relative triple coordinates. -/
def center (X Y : Boundary) (c : SU2) : CubeRelativeChart.Field := fun v =>
  unframe (fillGauge (fun k a => responseMatrix.mulVec (difference X Y c a) k) v.val)

theorem center_anchor (X Y : Boundary) (c : SU2) (a : Fin 3) :
    anchor (gaugeField (center X Y c)) a=responseMatrix.mulVec (difference X Y c a) := by
  let z : Fin 7 → Fin 3 → ℝ := fun k a => responseMatrix.mulVec (difference X Y c a) k
  let G := fillGauge z
  have hG : G root=0 := by simp [G,fillGauge,root]
  have he : gaugeField (center X Y c)=G := by
    funext v
    unfold gaugeField
    split_ifs with hv
    · rw [hv,hG]
    · exact frame_unframe _
  rw [he,show G=fillGauge z from rfl,anchor_fill]

/-- The Schur minimum is attained by genuine relative coordinate triples, not a surrogate field. -/
theorem minimum_attained (X Y : Boundary) (c : SU2) :
    ∃ Z : CubeRelativeChart.Field,mixedForm X Y c Z=effective X Y c := by
  refine ⟨center X Y c,?_⟩
  rw [completed_square]
  unfold remainder
  simp only [center_anchor,sub_self,Matrix.mulVec_zero,dotProduct_zero,
    Finset.sum_const_zero,zero_div,add_zero]


theorem effective_nonnegative (X Y : Boundary) (c : SU2) : 0 ≤ effective X Y c := by
  obtain ⟨Z,hZ⟩ := minimum_attained X Y c
  have hm : 0 ≤ CubeLocalKernel.mass Z := Finset.sum_nonneg
    (fun v _ => sub_nonneg.mpr (FourCubeHemisphereCoercivity.chartRate_ge_one (Z v)))
  calc
    0 ≤ CubeLocalKernel.mass Z/252 := div_nonneg hm (by norm_num)
    _ ≤ mixedForm X Y c Z := mixedForm_lower X Y c Z
    _ = _ := hZ

end OperatorDerivativeRewrite.Foundation.CubeRootSchur
