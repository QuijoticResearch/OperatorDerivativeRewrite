import Foundation.SU2HaarSmallCap
import Foundation.CubeChordTransfer
import Foundation.CubeGroundMass

/-! Quantitative actual Wilson blocks on reduced boundary caps and temporal Haar caps. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.CubePolynomialGround
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGround
open CubeAxialSlice CubeAxialGauge CubeHaarSplit CubeReducedHaar CubeChordTransfer
open SU2HaarSmallCap FourCubePinnedCoercivity
attribute [local irreducible] CubeWilsonSlab.kernel boundaryHaar gaugeHaar

def boundaryBox (t : ℝ) : Set State := reduced ⁻¹' (Set.univ.pi (fun _ : Fin 5 => cap t))
def temporalBox (t : ℝ) : Set Gauge := Set.univ.pi (fun _ : SpatialVertex => cap t)

theorem boundaryBox_measurable (t : ℝ) : MeasurableSet (boundaryBox t) :=
  (MeasurableSet.univ_pi (fun _ => cap_measurable t)).preimage reduced_measurable

theorem temporalBox_measurable (t : ℝ) : MeasurableSet (temporalBox t) :=
  MeasurableSet.univ_pi (fun _ => cap_measurable t)

theorem boundary_mass (t : ℝ) : boundaryHaar.real (boundaryBox t)=(law.real (cap t))^5 := by
  have h := Measure.map_apply reduced_measurable
    (MeasurableSet.univ_pi (fun _ : Fin 5 => cap_measurable t)) (μ := boundaryHaar)
  rw [reduced_preserving.map_eq] at h
  change (boundaryHaar (boundaryBox t)).toReal=(law (cap t)).toReal^5
  change (boundaryHaar (reduced ⁻¹' (Set.univ.pi (fun _ : Fin 5 => cap t)))).toReal = _
  rw [← h]
  simp only [chordHaar,Measure.pi_pi,ENNReal.toReal_prod,Finset.prod_const,Finset.card_univ,Fintype.card_fin, ENNReal.toReal_pow]

theorem temporal_mass (t : ℝ) : gaugeHaar.real (temporalBox t)=(law.real (cap t))^8 := by
  change (gaugeHaar (temporalBox t)).toReal=(law (cap t)).toReal^8
  simp only [gaugeHaar,temporalBox,Measure.pi_pi,ENNReal.toReal_prod,Finset.prod_const,
    Finset.card_univ,vertex_count, ENNReal.toReal_pow]

private theorem four_defect (U V W Z : SU2) :
    defect (U*V*W⁻¹*Z⁻¹) ≤ 9*(defect U+defect V+defect W+defect Z) := by
  have h1 := FourCubeBoundaryCoercivity.defect_mul (U*V) (W⁻¹*Z⁻¹)
  have h2 := FourCubeBoundaryCoercivity.defect_mul U V
  have h3 := FourCubeBoundaryCoercivity.defect_mul W⁻¹ Z⁻¹
  rw [defect_inv,defect_inv] at h3
  have he : U*V*W⁻¹*Z⁻¹=(U*V)*(W⁻¹*Z⁻¹) := by group
  rw [he]
  linarith

theorem axial_link_bound (t : ℝ) (q : Chords) (hq : ∀ i,q i ∈ cap t) (e : SpatialEdge) :
    defect (axialState q e) ≤ 3*t^2 := by
  unfold axialState
  cases h : chordLabel e with
  | none => simp only [Option.elim_none,defect_one]; positivity
  | some i => exact hq i

private theorem spatial_upper (t : ℝ) (U : State) (hU : ∀ e,defect (U e) ≤ 3*t^2) :
    spatialAction U ≤ 648*t^2 := by
  have hp (p : SpatialFace) : defect (spatialWord U p) ≤ 108*t^2 := by
    have h := four_defect (U (faceEdge p 0)) (U (faceEdge p 1))
      (U (faceEdge p 2)) (U (faceEdge p 3))
    change defect (spatialWord U p) ≤ _ at h
    linarith [hU (faceEdge p 0),hU (faceEdge p 1),hU (faceEdge p 2),hU (faceEdge p 3)]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hp p)
  simp only [Finset.sum_const,Finset.card_univ,face_count,nsmul_eq_mul] at h
  change (∑ p : SpatialFace,defect (spatialWord U p)) ≤ _
  convert h using 1 <;> ring

private theorem temporal_upper (t : ℝ) (U V : State) (g : Gauge)
    (hU : ∀ e,defect (U e) ≤ 3*t^2) (hV : ∀ e,defect (V e) ≤ 3*t^2)
    (hg : ∀ v,defect (g v) ≤ 3*t^2) : temporalAction U V g ≤ 1296*t^2 := by
  have he (e : SpatialEdge) : defect (temporalWord U V g e) ≤ 108*t^2 := by
    have h := four_defect (U e) (g (shift e.val.1 e.val.2)) (V e) (g e.val.1)
    change defect (temporalWord U V g e) ≤ _ at h
    linarith [hU e,hV e,hg (shift e.val.1 e.val.2),hg e.val.1]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun e _ => he e)
  simp only [Finset.sum_const,Finset.card_univ,edge_count,nsmul_eq_mul] at h
  change (∑ e : SpatialEdge,defect (temporalWord U V g e)) ≤ _
  convert h using 1 <;> ring

/-- Exact cap bound reused for genuine relative temporal Haar integration. -/
theorem action_cap_upper (t : ℝ) (U V : State) (g : Gauge)
    (hU : ∀ e,defect (U e) ≤ 3*t^2) (hV : ∀ e,defect (V e) ≤ 3*t^2)
    (hg : ∀ v,defect (g v) ≤ 3*t^2) : halfAction U V g ≤ 1944*t^2 := by
  have hA := spatial_upper t U hU
  have hB := spatial_upper t V hV
  have hT := temporal_upper t U V g hU hV hg
  unfold halfAction
  linarith

/-- A genuine positive-Haar block of the actual gauge-averaged homogeneous kernel. -/
theorem kernel_block (beta t : ℝ) (hb : 0 ≤ beta) (U V : State)
    (hU : U ∈ boundaryBox t) (hV : V ∈ boundaryBox t) :
    (law.real (cap t))^8*Real.exp (-1944*beta*t^2) ≤ kernel beta U V := by
  have hu (i : Fin 5) : reduced U i ∈ cap t := hU i (Set.mem_univ i)
  have hv (i : Fin 5) : reduced V i ∈ cap t := hV i (Set.mem_univ i)
  have hA := spatial_upper t (axialState (reduced U)) (axial_link_bound t _ hu)
  have hB := spatial_upper t (axialState (reduced V)) (axial_link_bound t _ hv)
  have hpoint (g : Gauge) (hg : g ∈ temporalBox t) :
      Real.exp (-1944*beta*t^2) ≤ weight beta (axialState (reduced U)) (axialState (reduced V)) g := by
    have hg' (v : SpatialVertex) : defect (g v) ≤ 3*t^2 := hg v (Set.mem_univ v)
    have hT := temporal_upper t _ _ g (axial_link_bound t _ hu) (axial_link_bound t _ hv) hg'
    have hh : halfAction (axialState (reduced U)) (axialState (reduced V)) g ≤ 1944*t^2 := by
      unfold halfAction
      linarith
    apply Real.exp_le_exp.mpr
    change -1944*beta*t^2 ≤ -beta*halfAction _ _ g
    nlinarith [mul_le_mul_of_nonneg_left hh hb]
  have hi := setIntegral_mono_on (integrable_const (Real.exp (-1944*beta*t^2))).integrableOn
    (weight_integrable beta (axialState (reduced U)) (axialState (reduced V))).integrableOn
    (temporalBox_measurable t) hpoint
  rw [setIntegral_const,smul_eq_mul,temporal_mass] at hi
  have hj := setIntegral_le_integral (s := temporalBox t)
    (weight_integrable beta (axialState (reduced U)) (axialState (reduced V)))
    (ae_of_all gaugeHaar (fun g => (Real.exp_pos _).le))
  rw [kernel_reduced beta U V,CubeWilsonSlab.kernel]
  exact hi.trans hj

variable {beta : ℝ} (d : GroundData beta)

/-- Polynomial block estimate for the actual constructed eigenvalue. -/
theorem eigenvalue_cap_lower (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (hb : 0 ≤ beta) :
    (law.real (cap t))^13*Real.exp (-1944*beta*t^2) ≤ d.value := by
  have hp : 0 < law.real (cap t) :=
    (mul_pos (by positivity : 0 < 1/(4*Real.pi^2)) (pow_pos ht 3)).trans_le (mass_lower t ht.le h1)
  have hm : 0 < boundaryHaar.real (boundaryBox t) := by rw [boundary_mass]; exact pow_pos hp 5
  have h := CubeGroundMass.eigenvalue_block_lower d (boundaryBox t) (boundaryBox_measurable t) hm
    ((law.real (cap t))^8*Real.exp (-1944*beta*t^2)) (fun U hU V hV => kernel_block beta t hb U V hU hV)
  rw [boundary_mass] at h
  convert h using 1 <;> ring

def lowerConstant : ℝ := (1/(4*Real.pi^2))^13*Real.exp (-1944)

theorem lowerConstant_pos : 0 < lowerConstant := by unfold lowerConstant; positivity

/-- A fixed positive constant times t^39 bounds the ACTUAL native eigenvalue below.
The power is deliberately nonsharp; no Gaussian normalization is assumed. -/
theorem eigenvalue_polynomial (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (hb : 0 ≤ beta) (hscale : beta*t^2 ≤ 1) : lowerConstant*t^39 ≤ d.value := by
  have hm := pow_le_pow_left₀
    (mul_nonneg (by positivity : 0 ≤ 1/(4*Real.pi^2)) (pow_nonneg ht.le 3)) (mass_lower t ht.le h1) 13
  have hm' : (1/(4*Real.pi^2))^13*t^39 ≤ (law.real (cap t))^13 := by
    convert hm using 1 <;> ring
  have he : Real.exp (-1944) ≤ Real.exp (-1944*beta*t^2) := Real.exp_le_exp.mpr (by nlinarith)
  have hp := mul_le_mul hm' he (Real.exp_pos (-1944)).le (pow_nonneg measureReal_nonneg 13)
  have h := hp.trans (eigenvalue_cap_lower d t ht h1 hb)
  convert h using 1 <;> unfold lowerConstant <;> ring

end OperatorDerivativeRewrite.Foundation.CubePolynomialGround
