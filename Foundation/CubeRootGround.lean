import Foundation.CubeTemporalRootHaar
import Foundation.CubeLogWindow

/-! Actual Wilson normalization with a free temporal root: twelve, not thirteen, Haar caps. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.CubeRootGround
open QuaternionSU2Representation CubeTemporalSlab CubeWilsonSlab CubeSlabGauge CubeSlabGround
open CubeAxialSlice CubeAxialGauge CubeChordTransfer CubePolynomialGround SU2HaarSmallCap
open CubeTemporalRootHaar FourCubePinnedCoercivity
attribute [local irreducible] CubeWilsonSlab.kernel weight boundaryHaar gaugeHaar

theorem temporal_word_assemble (c : SU2) (h : Relative) (U V : State) (e : SpatialEdge) :
    temporalWord U V (assemble c h) e=
      temporalWord U (gaugeAction (fun _ => c) V) (anchored h) e := by
  unfold temporalWord gaugeAction assemble
  group

theorem halfAction_assemble (c : SU2) (h : Relative) (U V : State) :
    halfAction U V (assemble c h)=halfAction U (gaugeAction (fun _ => c) V) (anchored h) := by
  have ht : temporalAction U V (assemble c h)=
      temporalAction U (gaugeAction (fun _ => c) V) (anchored h) := by
    unfold temporalAction
    simp_rw [temporal_word_assemble]
  unfold halfAction
  rw [ht,spatial_action_invariant]

theorem weight_assemble (beta : ℝ) (c : SU2) (h : Relative) (U V : State) :
    weight beta U V (assemble c h)=weight beta U (gaugeAction (fun _ => c) V) (anchored h) := by
  unfold weight
  rw [halfAction_assemble]

/-- Full product-Haar average, including the genuine free conjugating root. -/
theorem kernel_root_average (beta : ℝ) (U V : State) :
    kernel beta U V=∫ p : SU2 × Relative,
      weight beta U (gaugeAction (fun _ => p.1) V) (anchored p.2) ∂law.prod relativeHaar := by
  have hm : Measurable (weight beta U V) := by
    have hc : Measurable (fun g : Gauge => ((U,V),g)) := measurable_const.prodMk measurable_id
    exact (weight_joint_measurable beta).comp hc
  rw [CubeWilsonSlab.kernel,integral_split _ hm]
  simp_rw [weight_assemble]

/-- The two iterated integrals are genuine Bochner integrals, not a formal Fubini step. -/
theorem kernel_root_iterated (beta : ℝ) (U V : State) :
    kernel beta U V=∫ c,∫ h,weight beta U (gaugeAction (fun _ => c) V) (anchored h)
      ∂relativeHaar ∂law := by
  have hi := assemble_preserving.integrable_comp_of_integrable (weight_integrable beta U V)
  change Integrable (fun p : SU2 × Relative => weight beta U V (assemble p.1 p.2))
    (law.prod relativeHaar) at hi
  simp_rw [weight_assemble] at hi
  rw [kernel_root_average,integral_prod _ hi]

private theorem conjugated_cap (t : ℝ) (c : SU2) (V : State)
    (hV : ∀ e,defect (V e) ≤ 3*t^2) (e : SpatialEdge) :
    defect (gaugeAction (fun _ => c) V e) ≤ 3*t^2 := by
  simpa only [gaugeAction,defect,halfTrace_conjugate] using hV e

/-- Every relative-cap cylinder retains ALL possible root values. -/
theorem action_cylinder_upper (t : ℝ) (U V : State)
    (hU : ∀ e,defect (U e) ≤ 3*t^2) (hV : ∀ e,defect (V e) ≤ 3*t^2)
    (g : Gauge) (hg : g ∈ cylinder t) : halfAction U V g ≤ 1944*t^2 := by
  rw [← assemble_relative g,halfAction_assemble]
  exact action_cap_upper t U _ _ hU (conjugated_cap t _ V hV) (anchored_cap t _ hg)

/-- Actual integrated kernel block with SEVEN relative temporal caps. -/
theorem kernel_block (beta t : ℝ) (hb : 0 ≤ beta) (U V : State)
    (hU : U ∈ boundaryBox t) (hV : V ∈ boundaryBox t) :
    (law.real (cap t))^7*Real.exp (-1944*beta*t^2) ≤ kernel beta U V := by
  have hu (i : Fin 5) : reduced U i ∈ cap t := hU i (Set.mem_univ i)
  have hv (i : Fin 5) : reduced V i ∈ cap t := hV i (Set.mem_univ i)
  have hpoint (g : Gauge) (hg : g ∈ cylinder t) : Real.exp (-1944*beta*t^2) ≤
      weight beta (axialState (reduced U)) (axialState (reduced V)) g := by
    have hA := action_cylinder_upper t _ _ (axial_link_bound t _ hu) (axial_link_bound t _ hv) g hg
    unfold weight
    apply Real.exp_le_exp.mpr
    change -1944*beta*t^2 ≤ -beta*halfAction _ _ g
    nlinarith [mul_le_mul_of_nonneg_left hA hb]
  have hi := setIntegral_mono_on (integrable_const (Real.exp (-1944*beta*t^2))).integrableOn
    (weight_integrable beta (axialState (reduced U)) (axialState (reduced V))).integrableOn
    (cylinder_measurable t) hpoint
  rw [setIntegral_const,smul_eq_mul,cylinder_mass] at hi
  have hj := setIntegral_le_integral (s := cylinder t)
    (weight_integrable beta (axialState (reduced U)) (axialState (reduced V)))
    (ae_of_all gaugeHaar (fun _ => by unfold weight; exact (Real.exp_pos _).le))
  rw [kernel_reduced beta U V,CubeWilsonSlab.kernel]
  exact hi.trans hj

variable {beta : ℝ} (d : GroundData beta)

theorem eigenvalue_cap_lower (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (hb : 0 ≤ beta) :
    (law.real (cap t))^12*Real.exp (-1944*beta*t^2) ≤ d.value := by
  have hp : 0 < law.real (cap t) :=
    (mul_pos (by positivity : 0 < 1/(4*Real.pi^2)) (pow_pos ht 3)).trans_le (mass_lower t ht.le h1)
  have hm : 0 < boundaryHaar.real (boundaryBox t) := by rw [boundary_mass]; exact pow_pos hp 5
  have h := CubeGroundMass.eigenvalue_block_lower d (boundaryBox t) (boundaryBox_measurable t) hm
    ((law.real (cap t))^7*Real.exp (-1944*beta*t^2)) (fun U hU V hV => kernel_block beta t hb U V hU hV)
  rw [boundary_mass] at h
  convert h using 1 <;> ring

def lowerConstant : ℝ := (1/(4*Real.pi^2))^12*Real.exp (-1944)
theorem lowerConstant_pos : 0 < lowerConstant := by unfold lowerConstant; positivity

/-- Actual beta^(-18)-scale lower bound after retaining the full global root.
This is only a lower bound, not a matched asymptotic or a spectral-gap theorem. -/
theorem eigenvalue_polynomial (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1)
    (hb : 0 ≤ beta) (hscale : beta*t^2 ≤ 1) : lowerConstant*t^36 ≤ d.value := by
  have hm := pow_le_pow_left₀
    (mul_nonneg (by positivity : 0 ≤ 1/(4*Real.pi^2)) (pow_nonneg ht.le 3)) (mass_lower t ht.le h1) 12
  have hm' : (1/(4*Real.pi^2))^12*t^36 ≤ (law.real (cap t))^12 := by
    convert hm using 1 <;> ring
  have he : Real.exp (-1944) ≤ Real.exp (-1944*beta*t^2) := Real.exp_le_exp.mpr (by nlinarith)
  have hp := mul_le_mul hm' he (Real.exp_pos (-1944)).le (pow_nonneg measureReal_nonneg 12)
  have h := hp.trans (eigenvalue_cap_lower d t ht h1 hb)
  convert h using 1 <;> unfold lowerConstant <;> ring


private theorem window_numerator (t : ℝ) (ht : 0 < t) :
    Real.exp (-(1/t^2)*CubeLogWindow.window t/2)=t^40 := by
  have he : -(1/t^2)*CubeLogWindow.window t/2=(40:ℕ)*Real.log t := by
    simp only [CubeLogWindow.window,one_div,Real.log_inv]
    field_simp [ht.ne'] <;> ring
  rw [he,Real.exp_nat_mul,Real.exp_log ht]

/-- The same shrinking window now has an O(t^4) actual native tail factor. -/
theorem eigenfactor_window (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (g : GroundData (1/t^2)) :
    Real.exp (-(1/t^2)*CubeLogWindow.window t/2)/g.value ≤ (1/lowerConstant)*t^4 := by
  have hs : (1/t^2)*t^2=1 := by field_simp [ht.ne']
  have hl := eigenvalue_polynomial g t ht h1 (by positivity) hs.le
  rw [window_numerator t ht]
  have hd := div_le_div_of_nonneg_left (pow_nonneg ht.le 40)
    (mul_pos lowerConstant_pos (pow_pos ht 36)) hl
  have he : t^40/(lowerConstant*t^36)=(1/lowerConstant)*t^4 := by
    field_simp [lowerConstant_pos.ne',ht.ne'] <;> ring
  exact hd.trans_eq he

/-- Quantitative native compression using the actual free-root normalization. -/
theorem compression (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (g : GroundData (1/t^2))
    (f : CubeSlabL2.StateL2 g) :
    ‖CubeSlabL2.operator g f-CubeNativeCompression.lowPart g (CubeLogWindow.window t)
      (CubeSlabL2.operator g (CubeNativeCompression.lowPart g (CubeLogWindow.window t) f))‖ ≤
      (2/lowerConstant)*t^4*‖f‖ := by
  have h := (CubeNativeCompression.compression_error g (by positivity) (CubeLogWindow.window t) f).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (eigenfactor_window t ht h1 g) (by norm_num : (0:ℝ) ≤ 2))
      (norm_nonneg f))
  convert h using 1 <;> ring

/-- Actual stationary probability outside the shrinking window is O(t^8). -/
theorem stationary_tail (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (g : GroundData (1/t^2)) :
    g.stationary.real {U | CubeLogWindow.window t ≤ spatialAction U} ≤ ((1/lowerConstant)*t^4)^2 := by
  have h := CubeGroundMass.action_tail_eigenfactor g (by positivity) (CubeLogWindow.window t)
  have hx (x : ℝ) : Real.exp x=(Real.exp (x/2))^2 := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have he : Real.exp (-(1/t^2)*CubeLogWindow.window t)/g.value^2=
      (Real.exp (-(1/t^2)*CubeLogWindow.window t/2)/g.value)^2 := by
    rw [div_pow]
    exact congrArg (fun z : ℝ => z/g.value^2) (hx (-(1/t^2)*CubeLogWindow.window t))
  rw [he] at h
  exact h.trans (pow_le_pow_left₀ (div_nonneg (Real.exp_pos _).le g.value_pos.le)
    (eigenfactor_window t ht h1 g) 2)

end OperatorDerivativeRewrite.Foundation.CubeRootGround
