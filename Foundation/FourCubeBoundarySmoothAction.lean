import Foundation.FourCubeHaarContinuousIntegral

/-! Supremum-norm smoothness of the actual three-boundary-axis finite-cell action. -/
noncomputable section
open scoped Topology ContDiff Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeBoundarySmoothAction
open QuaternionSU2Representation SU2JointPlaquetteCubic SU2TraceHessianModel
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubeIntegratedCubic FourCubeHaarParity FourCubeHaarChannels FourCubeWilsonCubic
open FourCubeHaarContinuousIntegral
attribute [local irreducible] edges upperFaces innerFaces

def axisMatrix (i : Fin 3) (t : ℝ) : M2 :=
  Real.cos t • (1 : M2)+Real.sin t • SU2MatrixExponentialBridge.algebraElement (SU2AxisMatrixJets.axisVector i 1)

theorem axisMatrix_eq (i : Fin 3) (t : ℝ) : axisMatrix i t=(axis i t : M2) :=
  (SU2AxisMatrixJets.axis_matrix_formula i t).symm

theorem axisMatrix_contDiff (i : Fin 3) : ContDiff ℝ ∞ (axisMatrix i) := by
  unfold axisMatrix
  fun_prop

def boundaryMatrix (a : Parameters) : Boundary → M2
  | .inl c => if c.val=(capHigh FourCubeIntegratedCubic.chosen).val then axisMatrix 0 (a 0) else
      if c.val=(capLow FourCubeIntegratedCubic.chosen).val then axisMatrix 2 (-a 2) else 1
  | .inr p => if p.val=FourCubeIntegratedCubic.chosen.val then axisMatrix 1 (-a 1) else 1

theorem boundaryMatrix_eq (a : Parameters) (c : Boundary) :
    boundaryMatrix a c=(boundaryData (a 0) (a 1) (a 2) c : M2) := by
  cases c <;> simp only [boundaryMatrix,boundaryData] <;> split_ifs <;>
    simp [axisMatrix_eq,← SU2AxisMatrixJets.axis_inv]

theorem boundaryMatrix_contDiff (c : Boundary) : ContDiff ℝ ∞ (fun a => boundaryMatrix a c) := by
  cases c <;> simp only [boundaryMatrix] <;> split_ifs <;>
    first | exact contDiff_const | exact (axisMatrix_contDiff _).comp (by fun_prop)

theorem boundary_inverse (x y z : ℝ) (c : Boundary) :
    boundaryData (-x) (-y) (-z) c=(boundaryData x y z c)⁻¹ := by
  cases c <;> simp only [boundaryData] <;> split_ifs <;> simp [SU2AxisMatrixJets.axis_inv]

def wordMatrix (a : Parameters) (p : Upper) : M2 :=
  boundaryMatrix a (.inl (capHigh p))*boundaryMatrix (-a) (.inr p)*boundaryMatrix (-a) (.inl (capLow p))

theorem wordMatrix_eq (a : Parameters) (p : Upper) :
    wordMatrix a p=(FourCubeIntegratedCubic.word (boundaryData (a 0) (a 1) (a 2)) p : M2) := by
  unfold wordMatrix FourCubeIntegratedCubic.word
  simp only [boundaryMatrix_eq,Pi.neg_apply,boundary_inverse]
  rfl

theorem wordMatrix_contDiff (p : Upper) : ContDiff ℝ ∞ (fun a => wordMatrix a p) := by
  have h1 : ContDiff ℝ ∞ (fun a : Parameters => boundaryMatrix a (.inl (capHigh p))) :=
    boundaryMatrix_contDiff _
  have h2 : ContDiff ℝ ∞ (fun a : Parameters => boundaryMatrix (-a) (.inr p)) := by
    exact (boundaryMatrix_contDiff (.inr p)).comp contDiff_id.neg
  have h3 : ContDiff ℝ ∞ (fun a : Parameters => boundaryMatrix (-a) (.inl (capLow p))) := by
    exact (boundaryMatrix_contDiff (.inl (capLow p))).comp contDiff_id.neg
  unfold wordMatrix
  exact (h1.mul h2).mul h3

theorem core_continuous (e : EdgeData) : Continuous (fun s : InteriorState => coreField s e) := by
  by_cases he : e∈edges
  · simpa only [coreField,dif_pos he] using (continuous_apply (⟨e,he⟩ : Interior))
  · simp only [coreField,dif_neg he]
    exact continuous_const

theorem halfTrace_continuous : Continuous halfTrace := by
  have he : halfTrace=(fun A : SU2 => traceContinuous (A : M2)) := by
    funext A
    exact (traceContinuous_apply _).symm
  rw [he]
  exact traceContinuous.continuous.comp continuous_subtype_val

theorem internal_continuous : Continuous internalAction := by
  unfold internalAction innerAction faceAction
  apply continuous_finset_sum
  intro p _
  exact continuous_const.sub (halfTrace_continuous.comp
    ((((core_continuous _).mul (core_continuous _)).mul (core_continuous _).inv).mul (core_continuous _).inv))

def internal : Observables := ⟨internalAction,internal_continuous⟩

def action (a : Parameters) : Observables :=
  internal+ContinuousMap.const _ (48 : ℝ)-∑ p : Upper,probe (ribbonInterior p) (wordMatrix a p)

theorem probe_ribbon (a : Parameters) (p : Upper) (s : InteriorState) :
    probe (ribbonInterior p) (wordMatrix a p) s=ribbonChannel (boundaryData (a 0) (a 1) (a 2)) p s := by
  rw [probe_apply,wordMatrix_eq]
  rfl

theorem action_apply (a : Parameters) (s : InteriorState) : action a s=cellAction (a 0) (a 1) (a 2) s := by
  rw [cellAction,action_decomposition]
  simp only [action,ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.const_apply,
    ContinuousMap.sum_apply,internal,probe_ribbon,ribbonSum]
  rfl

theorem action_contDiff : ContDiff ℝ ∞ action := by
  have hs : ContDiff ℝ ∞ (fun a : Parameters => ∑ p : Upper,probe (ribbonInterior p) (wordMatrix a p)) := by
    apply ContDiff.sum
    intro p _
    exact (probe (ribbonInterior p)).contDiff.comp (wordMatrix_contDiff p)
  exact (contDiff_const.add contDiff_const).sub hs

end OperatorDerivativeRewrite.Foundation.FourCubeBoundarySmoothAction
