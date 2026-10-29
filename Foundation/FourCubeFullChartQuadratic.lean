import Foundation.FourCubeFullHaarCutoff

/-! Actual unpinned32 Haar-chart quadratic scaling, by verified four-link jets.
No pinned31 Hessian or Gaussian law is substituted for this action. -/
noncomputable section
open Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullChartQuadratic
open QuaternionSU2Representation SU2TraceHessianModel SU2MatrixExponentialBridge
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex OneSidedSourceRows
open FourCubeFullChartOdd FourCubeMovingBoundaryQuadratic FourCubePinnedCoercivity
open SU2GaussianConeCoordinates SU2HemisphereChart SU2FourCurveJetTransfer

attribute [local irreducible] edges innerFaces upperFaces

private theorem weight_contDiff (y : Triple) : ContDiff ℝ 2 (SU2HemisphereJets.weight y) := by
  have hp (t : ℝ) : 0<1+t^2*SU2HemisphereJets.sizeSq y := by
    have h := SU2HemisphereJets.sizeSq_nonneg y
    positivity
  have hb : ContDiff ℝ 2 (fun t : ℝ => 1+t^2*SU2HemisphereJets.sizeSq y) :=
    contDiff_const.add ((contDiff_id.pow 2).mul contDiff_const)
  exact (hb.sqrt (fun t => (hp t).ne')).inv (fun t => (Real.sqrt_pos.mpr (hp t)).ne')

private theorem curve_contDiff (y : Triple) : ContDiff ℝ 2 (SU2HemisphereJets.curve y) := by
  have ha : ContDiff ℝ 2 (SU2HemisphereJets.affine y) :=
    contDiff_const.add (contDiff_id.smul contDiff_const)
  convert! (weight_contDiff y).smul ha using 1
  funext t
  exact SU2HemisphereJets.curve_formula y t

private theorem quadratic_quotient (f : ℝ → ℝ) (q : ℝ) (hf : ContDiff ℝ 2 f)
    (h0 : f 0=0) (h1 : deriv f 0=0) (h2 : deriv (deriv f) 0=q) :
    Tendsto (fun t : ℝ => f t/t^2) (𝓝[≠] 0) (𝓝 (q/2)) := by
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

def pauliVelocity (Y : Coordinates) (x y z : ℝ) : FullEdge → Fin 3 → ℝ
  | .inl e => SU2HemisphereJets.frame (Y e)
  | .inr c => boundaryVector x y z c

def facePath (Y : Coordinates) (x y z : ℝ) (p : FullFace) (t : ℝ) : WordField :=
  fun i => (links Y x y z t (rowEdges p i) : M2)
def faceRay (Y : Coordinates) (x y z : ℝ) (p : FullFace) : ℝ → ℝ :=
  traceAction ∘ facePath Y x y z p

def faceQuadratic (Y : Coordinates) (x y z : ℝ) (p : FullFace) : ℝ :=
  lengthSq (pauliVelocity Y x y z (rowEdges p 0)+pauliVelocity Y x y z (rowEdges p 1)-
    pauliVelocity Y x y z (rowEdges p 2)-pauliVelocity Y x y z (rowEdges p 3))/4

def nativeQuadratic (Y : Coordinates) (x y z : ℝ) : ℝ := ∑ p : FullFace,faceQuadratic Y x y z p
def diagonalQuadratic (Y : Coordinates) : ℝ :=
  ∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*SU2HemisphereJets.sizeSq (Y e)
def completedQuadratic (Y : Coordinates) (x y z : ℝ) : ℝ :=
  nativeQuadratic Y x y z+diagonalQuadratic Y

theorem link_jets (Y : Coordinates) (x y z : ℝ) (e : FullEdge) :
    ContDiff ℝ 2 (fun t : ℝ => (links Y x y z t e : M2)) ∧
      (links Y x y z 0 e : M2)=1 ∧
      deriv (fun t : ℝ => (links Y x y z t e : M2)) 0=algebraElement (pauliVelocity Y x y z e) ∧
      deriv (deriv (fun t : ℝ => (links Y x y z t e : M2))) 0=
        (algebraElement (pauliVelocity Y x y z e))^2 := by
  cases e with
  | inl e =>
    exact ⟨curve_contDiff _,SU2HemisphereJets.curve_zero _,SU2HemisphereJets.curve_first_zero _,
      SU2HemisphereJets.curve_second_generator _⟩
  | inr c => exact boundary_jets x y z c

theorem face_jets (Y : Coordinates) (x y z : ℝ) (p : FullFace) :
    ContDiff ℝ 2 (faceRay Y x y z p) ∧ deriv (faceRay Y x y z p) 0=0 ∧
      deriv (deriv (faceRay Y x y z p)) 0=faceQuadratic Y x y z p := by
  exact trace_component_jets (facePath Y x y z p) (fun i => pauliVelocity Y x y z (rowEdges p i))
    (fun i => (link_jets Y x y z _).1) (fun i => (link_jets Y x y z _).2.1)
    (fun i => (link_jets Y x y z _).2.2.1) (fun i => (link_jets Y x y z _).2.2.2)

theorem face_zero (Y : Coordinates) (x y z : ℝ) (p : FullFace) : faceRay Y x y z p 0=0 := by
  simp [faceRay,facePath,Function.comp_def,traceAction,links_zero,traceReal,Matrix.trace_fin_two]

theorem face_actual (Y : Coordinates) (x y z t : ℝ) (p : FullFace) :
    faceRay Y x y z p t=SU2QuaternionOddWord.wordAction (FourCubeMovingOddAction.factors (links Y x y z t) p) := by
  rfl

theorem native_face_sum (Y : Coordinates) (x y z t : ℝ) :
    nativeRay Y x y z t=∑ p : FullFace,faceRay Y x y z p t := by
  rw [nativeRay,FourCubeMovingOddAction.fullAction_rows]
  apply Finset.sum_congr rfl
  intro p hp
  exact (face_actual Y x y z t p).symm

theorem face_quadratic_limit (Y : Coordinates) (x y z : ℝ) (p : FullFace) :
    Tendsto (fun t : ℝ => faceRay Y x y z p t/t^2) (𝓝[≠] 0) (𝓝 (faceQuadratic Y x y z p/2)) :=
  quadratic_quotient _ _ (face_jets Y x y z p).1 (face_zero Y x y z p)
    (face_jets Y x y z p).2.1 (face_jets Y x y z p).2.2

theorem native_quadratic_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => nativeRay Y x y z t/t^2) (𝓝[≠] 0) (𝓝 (nativeQuadratic Y x y z/2)) := by
  have h := tendsto_finsetSum Finset.univ (fun p _ => face_quadratic_limit Y x y z p)
  simpa only [native_face_sum,Finset.sum_div,nativeQuadratic] using h

theorem chart_defect (y : Triple) (t : ℝ) :
    defect (hemisphereChart (t • y))=1-SU2HemisphereJets.weight y t := by
  rw [defect,chart_halfTrace,SU2HemisphereJets.radius_smul]
  rfl

theorem defect_quadratic_limit (y : Triple) :
    Tendsto (fun t : ℝ => defect (hemisphereChart (t • y))/t^2)
      (𝓝[≠] 0) (𝓝 (SU2HemisphereJets.sizeSq y/2)) := by
  simp_rw [chart_defect]
  have hd : deriv (fun t : ℝ => 1-SU2HemisphereJets.weight y t)=
      fun t => -SU2HemisphereJets.weightSlope y t := by
    funext t
    exact ((SU2HemisphereJets.weight_hasDerivAt y t).const_sub 1).deriv
  apply quadratic_quotient _ _ (contDiff_const.sub (weight_contDiff y))
  · simp [SU2HemisphereJets.weight_zero]
  · rw [hd]
    simp [SU2HemisphereJets.weightSlope]
  · rw [hd]
    simpa using (SU2HemisphereJets.weightSlope_hasDerivAt_zero y).neg.deriv

theorem diagonal_quadratic_limit (Y : Coordinates) :
    Tendsto (fun t : ℝ => FourCubeCompletedHaar.diagonal (state Y t)/t^2)
      (𝓝[≠] 0) (𝓝 (diagonalQuadratic Y/2)) := by
  have h := tendsto_finsetSum Finset.univ (fun e _ =>
    (defect_quadratic_limit (Y e)).const_mul (FourCubeNegativeCompletion.multiplicity e : ℝ))
  have he (t : ℝ) : (∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*
      (defect (hemisphereChart (t • Y e))/t^2))=FourCubeCompletedHaar.diagonal (state Y t)/t^2 := by
    unfold FourCubeCompletedHaar.diagonal
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e he
    dsimp only [state]
    ring
  have hq : (∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*
      (SU2HemisphereJets.sizeSq (Y e)/2))=diagonalQuadratic Y/2 := by
    rw [diagonalQuadratic,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro e he
    ring
  simpa only [he,hq] using h

/-- The actual completed120-face path, with all32 chart coordinates retained. -/
theorem completed_quadratic_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => completedRay Y x y z t/t^2)
      (𝓝[≠] 0) (𝓝 (completedQuadratic Y x y z/2)) := by
  have h := (native_quadratic_limit Y x y z).add (diagonal_quadratic_limit Y)
  simp only [← add_div,← completed_native] at h
  simpa only [completedQuadratic,add_div] using h

theorem completed_boltzmann_limit (Y : Coordinates) (x y z : ℝ) :
    Tendsto (fun t : ℝ => Real.exp (-completedRay Y x y z t/t^2)) (𝓝[≠] 0)
      (𝓝 (Real.exp (-completedQuadratic Y x y z/2))) :=
  Real.continuous_exp.continuousAt.tendsto.comp
    (by simpa only [neg_div] using (completed_quadratic_limit Y x y z).neg)

end OperatorDerivativeRewrite.Foundation.FourCubeFullChartQuadratic
