import Foundation.SU2QuaternionOddWord
import Foundation.OneSidedSourceRows
import Mathlib.Analysis.Calculus.DSlope

/-! Cubic odd scaling of the actual full72-face moving-boundary Haar-chart action. -/
noncomputable section
open Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeMovingOddAction
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open FourCubePinnedHaar FourCubePinnedCoercivity FourCubeHemisphereCoercivity
open FourCubeMovingBoundaryQuadratic FourCubeMovingActionLimit FourCubeScaledBoundaryControl
open FourCubeHaarQuadraticLimit FourCubePinnedSecondVariation FourCubeIntegratedCubic
open SU2QuaternionOddWord
attribute [local irreducible] edges upperFaces innerFaces

abbrev Coordinates := FourCubeHemisphereCoercivity.Field

def links (Y : Coordinates) (x y z t : ℝ) : FullEdge → SU2 :=
  fill (movingBoundary t x y z) (fillPole 1 (chartField (t • Y)))

def velocity (Y : Coordinates) (x y z : ℝ) : FullEdge → M2
  | .inl e => SU2HemisphereJets.generator (liftVelocity Y e)
  | .inr c => algebraElement (boundaryVector x y z c)

theorem links_zero (Y : Coordinates) (x y z : ℝ) (e : FullEdge) : links Y x y z 0 e=1 := by
  apply Subtype.ext
  cases e with
  | inl e =>
    change (fillPole 1 (chartField ((0 : ℝ) • Y)) e : M2)=(1 : M2)
    rw [← ratio_coordinate_actual]
    exact SU2HemisphereJets.curve_zero _
  | inr c =>
    exact (boundary_jets x y z c).2.1

theorem links_hasDerivAt (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    HasDerivAt (fun t : ℝ => (links Y x y z t e : M2)) (velocity Y x y z e) 0 := by
  cases e with
  | inl e =>
    have he : (fun t : ℝ => (links Y x y z t (.inl e) : M2))=
        SU2HemisphereJets.curve (liftVelocity Y e) :=
      funext (fun t => (ratio_coordinate_actual Y t e).symm)
    rw [he]
    have hh := SU2HemisphereJets.curve_hasDerivAt (liftVelocity Y e) 0
    convert! hh using 1 <;> simp [velocity,SU2HemisphereJets.curveSlope,
      SU2HemisphereJets.weightSlope,SU2HemisphereJets.weight_zero,SU2HemisphereJets.affine]
  | inr c =>
    have hh : HasDerivAt (boundaryCurve x y z c) (deriv (boundaryCurve x y z c) 0) 0 :=
      ((boundary_jets x y z c).1.differentiable (by norm_num)).differentiableAt.hasDerivAt
    rw [(boundary_jets x y z c).2.2.1] at hh
    exact hh

private theorem chart_parity (u : SU2GaussianConeCoordinates.Triple) (t : ℝ) :
    SU2HemisphereJets.curve u (-t)=(SU2HemisphereJets.curve u t)ᴴ := by
  rw [SU2HemisphereJets.curve_formula,SU2HemisphereJets.curve_formula]
  have hw : SU2HemisphereJets.weight u (-t)=SU2HemisphereJets.weight u t := by
    simp [SU2HemisphereJets.weight]
  rw [hw]
  simp [SU2HemisphereJets.affine,Matrix.conjTranspose_smul,Matrix.conjTranspose_add,
    SU2HemisphereJets.generator,algebraElement_skewHermitian,neg_smul,smul_neg]

theorem links_parity (Y : Coordinates) (x y z t : ℝ) (e : FullEdge) :
    links Y x y z (-t) e=(links Y x y z t e)⁻¹ := by
  cases e with
  | inl e =>
    apply Subtype.ext
    change (fillPole 1 (chartField ((-t) • Y)) e : M2)=
      (fillPole 1 (chartField (t • Y)) e : M2)ᴴ
    rw [← ratio_coordinate_actual,← ratio_coordinate_actual]
    exact chart_parity _ t
  | inr c =>
    cases c <;> simp only [links,fill,movingBoundary,boundaryData] <;>
      split_ifs <;> simp [SU2AxisMatrixJets.axis_inv,neg_mul]

def factors (U : FullEdge → SU2) (p : FullFace) : Fin 4 → SU2 :=
  ![U (rowEdges p 0),U (rowEdges p 1),(U (rowEdges p 2))⁻¹,(U (rowEdges p 3))⁻¹]

def slopes (B : FullEdge → M2) (p : FullFace) : Fin 4 → M2 :=
  ![B (rowEdges p 0),B (rowEdges p 1),(B (rowEdges p 2))ᴴ,(B (rowEdges p 3))ᴴ]

def cubicCoefficient (Y : Coordinates) (x y z : ℝ) : ℝ :=
  ∑ p : FullFace,cubic (fun i => imagVector (recover (slopes (velocity Y x y z) p i)))

theorem factors_zero (Y : Coordinates) (x y z : ℝ) (p : FullFace) (i : Fin 4) :
    factors (links Y x y z 0) p i=1 := by
  fin_cases i <;> simp [factors,links_zero]

theorem factors_parity (Y : Coordinates) (x y z t : ℝ) (p : FullFace) (i : Fin 4) :
    factors (links Y x y z (-t)) p i=(factors (links Y x y z t) p i)⁻¹ := by
  fin_cases i <;> simp [factors,links_parity]

theorem factors_hasDerivAt (Y : Coordinates) (x y z : ℝ) (p : FullFace) (i : Fin 4) :
    HasDerivAt (fun t : ℝ => (factors (links Y x y z t) p i : M2))
      (slopes (velocity Y x y z) p i) 0 := by
  fin_cases i
  · exact links_hasDerivAt Y x y z _
  · exact links_hasDerivAt Y x y z _
  · change HasDerivAt (fun t : ℝ => (links Y x y z t (rowEdges p 2) : M2)ᴴ)
      ((velocity Y x y z (rowEdges p 2))ᴴ) 0
    exact FourCubeAmbientAction.adjointCLM.hasFDerivAt.comp_hasDerivAt 0 (links_hasDerivAt Y x y z _)
  · change HasDerivAt (fun t : ℝ => (links Y x y z t (rowEdges p 3) : M2)ᴴ)
      ((velocity Y x y z (rowEdges p 3))ᴴ) 0
    exact FourCubeAmbientAction.adjointCLM.hasFDerivAt.comp_hasDerivAt 0 (links_hasDerivAt Y x y z _)

private theorem retained_inner (U : FullEdge → SU2) (p : Inner) (i : Fin 4) :
    FourCubeBoundaryCubic.retained U (FourCubeChordIncidence.faceEdge p.val i)=U (.inl (innerEdges p i)) := by
  fin_cases i <;> simp [FourCubeBoundaryCubic.retained,FourCubeChordIncidence.faceEdge,innerEdges,
    (inner_edge_geometry p p.property).1,(inner_edge_geometry p p.property).2.1,
    (inner_edge_geometry p p.property).2.2.1,(inner_edge_geometry p p.property).2.2.2]

theorem fullAction_rows (U : FullEdge → SU2) :
    FourCubeBoundaryCubic.fullAction U=∑ p : FullFace,wordAction (factors U p) := by
  rw [FourCubeBoundaryCubic.fullAction,Fintype.sum_sum_type]
  congr 1
  · unfold FourCubeWilsonCubic.innerAction
    rw [← Finset.sum_coe_sort innerFaces]
    apply Finset.sum_congr rfl
    intro p _
    unfold FourCubeWilsonCubic.faceAction
    simp_rw [retained_inner]
    rfl

theorem movingRay_rows (Y : Coordinates) (x y z t : ℝ) :
    movingRay Y x y z t=∑ p : FullFace,wordAction (factors (links Y x y z t) p) :=
  fullAction_rows _

theorem actual_cubic_odd_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => (movingRay Y x y z t-movingRay Y x y z (-t))/(2*t^3))
      (𝓝[≠] 0) (𝓝 (cubicCoefficient Y x y z)) := by
  have hh := tendsto_finsetSum Finset.univ (fun p _ =>
    matrix_word_odd_limit (fun t => factors (links Y x y z t) p) (slopes (velocity Y x y z) p)
      (factors_zero Y x y z p) (fun t => factors_parity Y x y z t p) (factors_hasDerivAt Y x y z p))
  apply hh.congr'
  filter_upwards with t
  rw [movingRay_rows,movingRay_rows,← Finset.sum_sub_distrib,Finset.sum_div]

theorem actual_boltzmann_odd_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => (Real.exp (-movingRay Y x y z t/t^2)-
      Real.exp (-movingRay Y x y z (-t)/t^2))/(2*t)) (𝓝[≠] 0)
      (𝓝 (-cubicCoefficient Y x y z*Real.exp (-jointQuadratic Y x y z/2))) := by
  let A := fun t : ℝ => movingRay Y x y z t/t^2
  let O := fun t : ℝ => (movingRay Y x y z t-movingRay Y x y z (-t))/(2*t^3)
  let B := fun t : ℝ => A t-2*t*O t
  let D := fun t : ℝ => -2*t*O t
  have ha : Tendsto A (𝓝[≠] 0) (𝓝 (jointQuadratic Y x y z/2)) := moving_quadratic_limit Y x y z
  have ho : Tendsto O (𝓝[≠] 0) (𝓝 (cubicCoefficient Y x y z)) := actual_cubic_odd_limit Y x y z
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hd : Tendsto D (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero,zero_mul] using (ht.const_mul (-2)).mul ho
  have hb : Tendsto B (𝓝[≠] 0) (𝓝 (jointQuadratic Y x y z/2)) := by
    simpa only [mul_zero,zero_mul,sub_zero] using ha.sub ((ht.const_mul 2).mul ho)
  have hs : Tendsto (fun t => dslope Real.exp 0 (D t)) (𝓝[≠] 0) (𝓝 1) := by
    have hc := (continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt).tendsto.comp hd
    convert! hc using 1 <;> simp [dslope_same,Real.deriv_exp,Function.comp_def]
  have he := Real.continuous_exp.continuousAt.tendsto.comp hb.neg
  have hh := ((he.mul hs).mul ho).neg
  simp only [mul_one] at hh
  have htarget : -(Real.exp (-(jointQuadratic Y x y z/2))*cubicCoefficient Y x y z)=
      -cubicCoefficient Y x y z*Real.exp (-jointQuadratic Y x y z/2) := by rw [neg_div]; ring
  rw [htarget] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t htn
  have htn' : t ≠ 0 := htn
  have hbval : B t=movingRay Y x y z (-t)/t^2 := by
    dsimp [B,A,O]
    field_simp [htn']
    ring
  have hdiff := sub_smul_dslope Real.exp 0 (D t)
  simp only [sub_zero,smul_eq_mul,Real.exp_zero] at hdiff
  have hexp : Real.exp (-A t)=Real.exp (-B t)*Real.exp (D t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [A,B,D]
    ring
  change -(Real.exp (-B t)*dslope Real.exp 0 (D t)*O t)=_
  calc
    _ = Real.exp (-B t)*(D t*dslope Real.exp 0 (D t))/(2*t) := by
      dsimp [D]
      field_simp [htn'] <;> ring
    _ = Real.exp (-B t)*(Real.exp (D t)-1)/(2*t) := by rw [hdiff]
    _ = (Real.exp (-A t)-Real.exp (-B t))/(2*t) := by rw [hexp]; ring
    _ = _ := by rw [hbval]; simp only [A,neg_div]
end OperatorDerivativeRewrite.Foundation.FourCubeMovingOddAction
