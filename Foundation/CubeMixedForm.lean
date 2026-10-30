import Foundation.CubeKernelLimit
import Foundation.SU2MatrixJetTransfer

/-! Explicit mixed second-variation form of the actual slab, including its free-root adjoint. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeMixedForm
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeTemporalSlab CubeWilsonSlab CubeAxialSlice CubeChartAction CubeTemporalRootHaar
open CubeRelativeChart SU2TraceHessianModel SU2MatrixExponentialBridge
open SU2FourCurveJetTransfer SU2ProductCurveHessian
attribute [local irreducible] boundaryRay temporalRay chords

def edgeVelocity (X : Boundary) (e : SpatialEdge) : M2 :=
  (chordLabel e).elim 0 (fun i => SU2HemisphereJets.generator (X i))
def vertexVelocity (Z : CubeRelativeChart.Field) (v : SpatialVertex) : M2 :=
  if hv : v=root then 0 else SU2HemisphereJets.generator (Z ⟨v,hv⟩)
def adjointVelocity (c : SU2) (B : M2) : M2 := (c : M2)*B*(c : M2)ᴴ

def spatialCurl (X : Boundary) (p : SpatialFace) : M2 :=
  edgeVelocity X (faceEdge p 0)+edgeVelocity X (faceEdge p 1)-
    edgeVelocity X (faceEdge p 2)-edgeVelocity X (faceEdge p 3)
def temporalMix (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (e : SpatialEdge) : M2 :=
  edgeVelocity X e+vertexVelocity Z (shift e.val.1 e.val.2)-
    adjointVelocity c (edgeVelocity Y e)-vertexVelocity Z e.val.1

def mixedForm (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) : ℝ :=
  -(∑ p : SpatialFace,traceReal ((spatialCurl X p)^2))/8-
    (∑ p : SpatialFace,traceReal ((spatialCurl Y p)^2))/8-
    (∑ e : SpatialEdge,traceReal ((temporalMix X Y c Z e)^2))/4

private def Jet (f : ℝ → M2) (B : M2) : Prop :=
  ContDiff ℝ 2 f ∧ f 0=1 ∧ deriv f 0=B ∧ deriv (deriv f) 0=B^2

private theorem left_unitary (c : SU2) : (c : M2)ᴴ*(c : M2)=1 := by
  change ((c⁻¹*c : SU2) : M2)=(1 : M2)
  simp
private theorem right_unitary (c : SU2) : (c : M2)*(c : M2)ᴴ=1 := by
  change ((c*c⁻¹ : SU2) : M2)=(1 : M2)
  simp
private theorem adjoint_square (c : SU2) (B : M2) :
    adjointVelocity c (B^2)=(adjointVelocity c B)^2 := by
  unfold adjointVelocity
  calc
    _ = (c : M2)*B*((c : M2)ᴴ*(c : M2))*B*(c : M2)ᴴ := by rw [left_unitary]; noncomm_ring
    _ = _ := by noncomm_ring

private theorem constant_jet : Jet (fun _ : ℝ => (1 : M2)) 0 := by
  have hd : deriv (fun _ : ℝ => (1 : M2))=(fun _ : ℝ => (0 : M2)) :=
    funext (fun t => (hasDerivAt_const t (1 : M2)).deriv)
  refine ⟨contDiff_const,rfl,?_,?_⟩
  · rw [hd]
  · rw [hd]
    change deriv (fun _ : ℝ => (0 : M2)) (0 : ℝ)=(0 : M2)^2
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    exact (hasDerivAt_const (𝕜 := ℝ) (0 : ℝ) (0 : M2)).deriv

private theorem edge_jet (X : Boundary) (e : SpatialEdge) :
    Jet (fun t : ℝ => (boundaryRay X t e : M2)) (edgeVelocity X e) := by
  unfold Jet edgeVelocity boundaryRay axialState chords
  cases he : chordLabel e with
  | none => simp only [Option.elim_none]; exact constant_jet
  | some i => exact ⟨curve_contDiff _,SU2HemisphereJets.curve_zero _,
      SU2HemisphereJets.curve_first_zero _,SU2HemisphereJets.curve_second_generator _⟩

private def vertexCurve (Z : CubeRelativeChart.Field) (v : SpatialVertex) (t : ℝ) : M2 :=
  (anchored (chartField (t • Z)) v : M2)
private theorem vertex_jet (Z : CubeRelativeChart.Field) (v : SpatialVertex) :
    Jet (vertexCurve Z v) (vertexVelocity Z v) := by
  unfold Jet vertexCurve vertexVelocity anchored
  split_ifs with hv
  · exact constant_jet
  · exact ⟨curve_contDiff _,SU2HemisphereJets.curve_zero _,
      SU2HemisphereJets.curve_first_zero _,SU2HemisphereJets.curve_second_generator _⟩

private theorem deriv_adjoint (c : SU2) (f : ℝ → M2) (hf : Differentiable ℝ f) :
    deriv (fun t => adjointVelocity c (f t))=(fun t => adjointVelocity c (deriv f t)) := by
  funext t
  exact (((hf t).hasDerivAt.const_mul (c : M2)).mul_const (c : M2)ᴴ).deriv

private theorem conjugated_jet (c : SU2) (f : ℝ → M2) (B : M2) (h : Jet f B) :
    Jet (fun t => adjointVelocity c (f t)) (adjointVelocity c B) := by
  refine ⟨(contDiff_const.mul h.1).mul contDiff_const,?_,?_,?_⟩
  · change adjointVelocity c (f 0)=1
    rw [h.2.1]
    simpa only [adjointVelocity,mul_one] using right_unitary c
  · rw [deriv_adjoint c f (h.1.differentiable (by norm_num))]
    change adjointVelocity c (deriv f 0)=adjointVelocity c B
    rw [h.2.2.1]
  · rw [deriv_adjoint c f (h.1.differentiable (by norm_num)),
      deriv_adjoint c (deriv f) h.1.differentiable_deriv_two]
    change adjointVelocity c (deriv (deriv f) 0)=(adjointVelocity c B)^2
    rw [h.2.2.2,adjoint_square]

private theorem generator_skew (y : Triple) :
    (SU2HemisphereJets.generator y)ᴴ= -SU2HemisphereJets.generator y :=
  algebraElement_skewHermitian _
private theorem edge_skew (X : Boundary) (e : SpatialEdge) :
    (edgeVelocity X e)ᴴ= -edgeVelocity X e := by
  unfold edgeVelocity
  cases he : chordLabel e with
  | none => simp
  | some i => exact generator_skew _
private theorem vertex_skew (Z : CubeRelativeChart.Field) (v : SpatialVertex) :
    (vertexVelocity Z v)ᴴ= -vertexVelocity Z v := by
  unfold vertexVelocity
  split_ifs
  · simp
  · exact generator_skew _
private theorem adjoint_skew (c : SU2) (B : M2) (hB : Bᴴ= -B) :
    (adjointVelocity c B)ᴴ= -adjointVelocity c B := by
  simp only [adjointVelocity,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose,hB]
  simp only [mul_neg,neg_mul,mul_assoc]

private abbrev Rows := SpatialFace ⊕ (SpatialFace ⊕ SpatialEdge)
private def rowWeight : Rows → ℝ
  | .inl _ => 1/2
  | .inr (.inl _) => 1/2
  | .inr (.inr _) => 1
private def rowPath (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) : Rows → ℝ → WordField
  | .inl p => fun t i => (boundaryRay X t (faceEdge p i) : M2)
  | .inr (.inl p) => fun t i => (boundaryRay Y t (faceEdge p i) : M2)
  | .inr (.inr e) => fun t => ![(boundaryRay X t e : M2),vertexCurve Z (shift e.val.1 e.val.2) t,
      adjointVelocity c (boundaryRay Y t e : M2),vertexCurve Z e.val.1 t]
private def rowVelocity (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) : Rows → WordField
  | .inl p => fun i => edgeVelocity X (faceEdge p i)
  | .inr (.inl p) => fun i => edgeVelocity Y (faceEdge p i)
  | .inr (.inr e) => ![edgeVelocity X e,vertexVelocity Z (shift e.val.1 e.val.2),
      adjointVelocity c (edgeVelocity Y e),vertexVelocity Z e.val.1]
private def rowMix (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) : Rows → M2
  | .inl p => spatialCurl X p
  | .inr (.inl p) => spatialCurl Y p
  | .inr (.inr e) => temporalMix X Y c Z e

private theorem row_jet (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (r : Rows) (i : Fin 4) :
    Jet (fun t => rowPath X Y c Z r t i) (rowVelocity X Y c Z r i) := by
  cases r with
  | inl p => exact edge_jet X _
  | inr r => cases r with
    | inl p => exact edge_jet Y _
    | inr e =>
      fin_cases i
      · exact edge_jet X e
      · exact vertex_jet Z _
      · exact conjugated_jet c _ _ (edge_jet Y e)
      · exact vertex_jet Z _
private theorem row_skew (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (r : Rows) (i : Fin 4) :
    (rowVelocity X Y c Z r i)ᴴ= -rowVelocity X Y c Z r i := by
  cases r with
  | inl p => exact edge_skew X _
  | inr r => cases r with
    | inl p => exact edge_skew Y _
    | inr e =>
      fin_cases i
      · exact edge_skew X e
      · exact vertex_skew Z _
      · exact adjoint_skew c _ (edge_skew Y e)
      · exact vertex_skew Z _

private theorem row_contDiff (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (r : Rows) :
    ContDiff ℝ 2 (traceAction ∘ rowPath X Y c Z r) :=
  traceAction_contDiff.comp (contDiff_pi.mpr (fun i => (row_jet X Y c Z r i).1))
private theorem row_second (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (r : Rows) :
    deriv (deriv (traceAction ∘ rowPath X Y c Z r)) 0= -traceReal ((rowMix X Y c Z r)^2)/2 := by
  have h := SU2MatrixJetTransfer.trace_second (rowPath X Y c Z r) (rowVelocity X Y c Z r)
    (row_skew X Y c Z r) (fun i => (row_jet X Y c Z r i).1)
    (fun i => (row_jet X Y c Z r i).2.1) (fun i => (row_jet X Y c Z r i).2.2.1)
    (fun i => (row_jet X Y c Z r i).2.2.2)
  convert h using 1
  cases r with
  | inl p => rfl
  | inr r => cases r with
    | inl p => rfl
    | inr e => rfl

private theorem spatial_trace (X : Boundary) (p : SpatialFace) (t : ℝ) :
    (traceAction ∘ rowPath X X 1 0 (.inl p)) t=1-halfTrace (spatialWord (boundaryRay X t) p) := rfl

private theorem temporal_trace (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) (e : SpatialEdge) (t : ℝ) :
    traceAction (rowPath X Y c Z (.inr (.inr e)) t)=
      1-halfTrace (temporalWord (boundaryRay X t) (boundaryRay Y t) (temporalRay c Z t) e) := by
  unfold temporalRay
  rw [CubeRootGround.temporal_word_assemble]
  rfl

private theorem action_rows (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    actionRay X Y c Z=(fun t => ∑ r : Rows,rowWeight r*(traceAction ∘ rowPath X Y c Z r) t) := by
  funext t
  unfold actionRay halfAction spatialAction temporalAction
  simp only [Fintype.sum_sum_type,rowWeight,rowPath,Function.comp_apply,one_mul]
  simp_rw [← temporal_trace]
  have hs (A : Boundary) (p : SpatialFace) : 1-halfTrace (spatialWord (boundaryRay A t) p)=
      traceAction (fun i => (boundaryRay A t (faceEdge p i) : M2)) := rfl
  simp_rw [hs]
  simp only [rowPath]
  simp only [← Finset.mul_sum]
  ring

private theorem second_sum {ι : Type} [Fintype ι] (f : ι → ℝ → ℝ)
    (hf : ∀ i,ContDiff ℝ 2 (f i)) :
    deriv (deriv (fun t : ℝ => ∑ i,f i t)) 0=∑ i,deriv (deriv (f i)) 0 := by
  have hd : deriv (fun t : ℝ => ∑ i,f i t)=(fun t => ∑ i,deriv (f i) t) := by
    funext t
    convert! deriv_sum (u := Finset.univ) (fun i _ => ((hf i).differentiable (by norm_num)).differentiableAt) using 1
    congr 1
    funext u
    simp only [Finset.sum_apply]
  rw [hd]
  convert! deriv_sum (u := Finset.univ) (fun i _ => (hf i).differentiable_deriv_two.differentiableAt) using 1
  congr 1
  funext u
  simp only [Finset.sum_apply]

/-- Exact actual mixed quadratic coefficient, with adjoint root and spatial half-sharing. -/
theorem secondVariation_eq (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    secondVariation X Y c Z/2=mixedForm X Y c Z := by
  unfold secondVariation
  rw [action_rows,second_sum _ (fun r => contDiff_const.mul (row_contDiff X Y c Z r))]
  simp only [deriv_const_mul_field']
  simp_rw [row_second]
  simp only [Fintype.sum_sum_type,rowWeight,rowMix,one_mul,← Finset.mul_sum,← Finset.sum_div]
  unfold mixedForm
  simp only [Finset.sum_neg_distrib]
  ring


/-- The verified nonlinear confinement now bounds the explicit actual quadratic form. -/
theorem mixedForm_lower (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    CubeLocalKernel.mass Z/252 ≤ mixedForm X Y c Z := by
  rw [← secondVariation_eq]
  exact CubeKernelLimit.secondVariation_lower X Y c Z

/-- The actual limiting density has this explicit root-dependent matrix exponent. -/
theorem limitDensity_eq (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    CubeKernelLimit.limitDensity X Y (c,Z)=
      (chartDensity 0)^7*Real.exp (-mixedForm X Y c Z) := by
  simp only [CubeKernelLimit.limitDensity,neg_div,secondVariation_eq]

/-- Actual kernel limit with the explicit mixed form and complete Haar root average. -/
theorem kernel_tendsto (X Y : Boundary) :
    Tendsto (fun t : ℝ => kernel (1/t^2) (boundaryRay X t) (boundaryRay Y t)/t^21)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ p : SU2 × CubeRelativeChart.Field,
        (chartDensity 0)^7*Real.exp (-mixedForm X Y p.1 p.2) ∂law.prod volume)) := by
  simpa only [CubeKernelLimit.limitDensity,neg_div,secondVariation_eq] using
    CubeKernelLimit.kernel_tendsto X Y

end OperatorDerivativeRewrite.Foundation.CubeMixedForm
