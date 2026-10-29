import Foundation.FourCubeFullColorSymmetry

/-! Source-uniform polynomial/Gaussian envelope for the actual full32 odd quotient.
Only per-link and generic quaternion estimates are reused from the pinned argument. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeFullOddEnvelope
open QuaternionSU2Representation SU2QuaternionOddWord SU2TraceHessianModel
open SU2GaussianConeCoordinates
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubeFullChartOdd FourCubeFullChartDomination FourCubeFullHaarCutoff
open FourCubeMovingBoundaryQuadratic FourCubeScaledBoundaryControl
open FourCubeMovingOddAction (factors)
open FourCubeOddEnvelope (chart_component_bound axis_component_bound weightedCubic_bound exponential_difference_bound)

attribute [local irreducible] edges innerFaces upperFaces

def budget (Y : Coordinates) (x y z : ℝ) : ℝ := 1+mass Y+|x|+|y|+|z|

theorem mass_squares (Y : Coordinates) : mass Y=∑ e : Interior,∑ a : Fin 3,(Y e a)^2 := by
  unfold mass
  apply Finset.sum_congr rfl
  intro e he
  simp [chartRate,Fin.sum_univ_three]
  ring

theorem budget_positive (Y : Coordinates) (x y z : ℝ) : 0<budget Y x y z := by
  unfold budget
  linarith [mass_nonneg Y,abs_nonneg x,abs_nonneg y,abs_nonneg z]

theorem coordinate_bound (Y : Coordinates) (x y z : ℝ) (e : Interior) (a : Fin 3) :
    |Y e a| ≤ budget Y x y z := by
  have h1 : (Y e a)^2 ≤ ∑ b : Fin 3,(Y e b)^2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have h2 : (∑ b : Fin 3,(Y e b)^2) ≤ mass Y := by
    rw [mass_squares]
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)) (Finset.mem_univ e)
  have hh := sq_abs (Y e a)
  unfold budget
  nlinarith [sq_nonneg (|Y e a|-1),mass_nonneg Y,abs_nonneg x,abs_nonneg y,abs_nonneg z]

theorem links_component_bound (Y : Coordinates) (x y z t : ℝ) (ht : t ≠ 0)
    (e : FullEdge) (a : Fin 3) :
    |imagVector (recover (links Y x y z t e : M2)) a/t| ≤ budget Y x y z := by
  have hb (k : Fin 3) (r : ℝ) (hr : |r| ≤ budget Y x y z) :
      |imagVector (recover (SU2JointPlaquetteCubic.axis k (t*r) : M2)) a/t| ≤ budget Y x y z :=
    (axis_component_bound k r t ht a).trans hr
  have hx : |x| ≤ budget Y x y z := by unfold budget; linarith [mass_nonneg Y,abs_nonneg y,abs_nonneg z]
  have hy : |-y| ≤ budget Y x y z := by rw [abs_neg]; unfold budget; linarith [mass_nonneg Y,abs_nonneg x,abs_nonneg z]
  have hz : |-z| ≤ budget Y x y z := by rw [abs_neg]; unfold budget; linarith [mass_nonneg Y,abs_nonneg x,abs_nonneg y]
  cases e with
  | inl e =>
    have he : (links Y x y z t (.inl e) : M2)=SU2HemisphereJets.curve (Y e) t :=
      rfl
    rw [he]
    exact (chart_component_bound _ t ht a).trans (coordinate_bound Y x y z e a)
  | inr c =>
    cases c <;> simp only [links,FourCubeIntegratedCubic.fill,movingBoundary,FourCubeIntegratedCubic.boundaryData] <;> split_ifs
    all_goals first
      | simpa [SU2AxisMatrixJets.axis_inv,mul_neg] using hb 0 x hx
      | simpa [SU2AxisMatrixJets.axis_inv,mul_neg] using hb 1 (-y) hy
      | simpa [SU2AxisMatrixJets.axis_inv,mul_neg] using hb 2 (-z) hz
      | fin_cases a <;> simpa [imagVector,recover] using (budget_positive Y x y z).le

theorem factors_component_bound (Y : Coordinates) (x y z t : ℝ) (ht : t ≠ 0)
    (p : FullFace) (i : Fin 4) (a : Fin 3) :
    |imagVector (recover (factors (links Y x y z t) p i : M2)) a/t| ≤ budget Y x y z := by
  fin_cases i
  · exact links_component_bound Y x y z t ht _ a
  · exact links_component_bound Y x y z t ht _ a
  · change |imagVector (recover (((links Y x y z t (OneSidedSourceRows.rowEdges p 2))⁻¹ : SU2) : M2)) a/t| ≤ _
    rw [recover_inverse]
    have hh := links_component_bound Y x y z t ht (OneSidedSourceRows.rowEdges p 2) a
    fin_cases a <;> simpa [imagVector,abs_div,abs_neg] using hh
  · change |imagVector (recover (((links Y x y z t (OneSidedSourceRows.rowEdges p 3))⁻¹ : SU2) : M2)) a/t| ≤ _
    rw [recover_inverse]
    have hh := links_component_bound Y x y z t ht (OneSidedSourceRows.rowEdges p 3) a
    fin_cases a <;> simpa [imagVector,abs_div,abs_neg] using hh

theorem face_odd_bound (Y : Coordinates) (x y z t : ℝ) (ht : t ≠ 0) (p : FullFace) :
    |(wordAction (factors (links Y x y z t) p)-
      wordAction (factors (links Y x y z (-t)) p))/(2*t^3)| ≤ 24*(budget Y x y z)^3 := by
  rw [wordAction_raw,wordAction_raw]
  have hp : (fun i => recover (factors (links Y x y z (-t)) p i : M2))=
      (fun i => star (recover (factors (links Y x y z t) p i : M2))) := by
    funext i
    rw [factors_parity,recover_inverse]
  rw [hp,odd_quotient _ t ht]
  apply weightedCubic_bound _ _ _ (budget_positive Y x y z).le
  · intro i
    rw [← SU2HemisphereChart.halfTrace_recover]
    exact halfTrace_bound _
  · exact fun i a => factors_component_bound Y x y z t ht p i a

theorem actual_odd_bound (Y : Coordinates) (x y z t : ℝ) (ht : t ≠ 0) :
    |(nativeRay Y x y z t-nativeRay Y x y z (-t))/(2*t^3)| ≤ 1728*(budget Y x y z)^3 := by
  rw [nativeRay,nativeRay,FourCubeMovingOddAction.fullAction_rows,FourCubeMovingOddAction.fullAction_rows,← Finset.sum_sub_distrib,Finset.sum_div]
  calc
    _ ≤ ∑ p : FullFace,|(wordAction (factors (links Y x y z t) p)-
        wordAction (factors (links Y x y z (-t)) p))/(2*t^3)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : FullFace,24*(budget Y x y z)^3 :=
      Finset.sum_le_sum (fun p _ => face_odd_bound Y x y z t ht p)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,fullFace_card,nsmul_eq_mul,Nat.cast_ofNat]; ring

theorem completed_odd_bound (Y : Coordinates) (x y z t : ℝ) (ht : t≠0) :
    |(completedRay Y x y z t-completedRay Y x y z (-t))/(2*t^3)| ≤ 1728*(budget Y x y z)^3 := by
  rw [completed_odd_identity]
  exact actual_odd_bound Y x y z t ht

theorem cutoff_neg (t : ℝ) (Y : Coordinates) : (-t) • Y∈coordinateCutoff ↔ t • Y∈coordinateCutoff := by
  have he (e : Interior) : chartRate ((-t) • Y e)=chartRate (t • Y e) := by
    simp [chartRate,Pi.smul_apply,smul_eq_mul]
  change (∀ e,chartRate ((-t) • Y e) ≤ 2) ↔ _
  simp only [he]
  rfl

/-- No source-dependent exponential loss: the completed cutoff coercivity is uniform. -/
theorem scaled_exponent_bound (Y : Coordinates) (x y z t : ℝ) (ht : t≠0)
    (hY : t • Y∈coordinateCutoff) : -completedRay Y x y z t/t^2 ≤ -mass Y/4 := by
  have hp : 0 ≤ 1/t^2 := by positivity
  have hc : (1/t^2)*t^2=1 := by field_simp [ht]
  have h := scaled_completed_lower (FourCubeFullHaarGaussianLimit.parameters x y z t) (1/t^2) t hp hc Y hY
  change mass Y/4 ≤ (1/t^2)*completedRay Y x y z t at h
  have he : (1/t^2)*completedRay Y x y z t=completedRay Y x y z t/t^2 := by ring
  rw [he] at h
  simpa only [neg_div] using neg_le_neg h

theorem completed_boltzmann_odd_bound (Y : Coordinates) (x y z t : ℝ) (ht : t≠0)
    (hY : t • Y∈coordinateCutoff) :
    |(Real.exp (-completedRay Y x y z t/t^2)-Real.exp (-completedRay Y x y z (-t)/t^2))/(2*t)| ≤
      (1728*(budget Y x y z)^3)*Real.exp (-mass Y/4) := by
  let R : ℝ := -mass Y/4
  have hp : -completedRay Y x y z t/t^2 ≤ R := scaled_exponent_bound Y x y z t ht hY
  have hm : -completedRay Y x y z (-t)/t^2 ≤ R := by
    simpa only [neg_sq] using scaled_exponent_bound Y x y z (-t) (neg_ne_zero.mpr ht) ((cutoff_neg t Y).mpr hY)
  have hh := exponential_difference_bound _ _ R hp hm
  have hd : ((-completedRay Y x y z t/t^2)-(-completedRay Y x y z (-t)/t^2))/(2*t)=
      -((completedRay Y x y z t-completedRay Y x y z (-t))/(2*t^3)) := by
    field_simp [ht]
    ring
  rw [abs_div]
  calc
    _ ≤ (Real.exp R*|(-completedRay Y x y z t/t^2)-(-completedRay Y x y z (-t)/t^2)|)/|2*t| :=
      div_le_div_of_nonneg_right hh (abs_nonneg _)
    _ = Real.exp R*|(completedRay Y x y z t-completedRay Y x y z (-t))/(2*t^3)| := by
      rw [mul_div_assoc,← abs_div,hd,abs_neg]
    _ ≤ Real.exp R*(1728*(budget Y x y z)^3) :=
      mul_le_mul_of_nonneg_left (completed_odd_bound Y x y z t ht) (Real.exp_pos _).le
    _ = _ := by dsimp [R]; ring

theorem wider_gaussian_integrable : Integrable (fun Y : Coordinates => Real.exp (-mass Y/8)) := by
  have hs : Real.sqrt (2 : ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have h := gaussian_majorant_integrable.comp_smul (inv_ne_zero hs)
  convert! h using 1
  funext Y
  rw [mass_smul,inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem cubic_weight_integrable (x y z : ℝ) :
    Integrable (fun Y : Coordinates => (budget Y x y z)^3*Real.exp (-mass Y/4)) := by
  let K := 6*(8 : ℝ)^3*Real.exp ((1+|x|+|y|+|z|)/8)
  have hm : Measurable (fun Y : Coordinates => (budget Y x y z)^3*Real.exp (-mass Y/4)) := by
    unfold budget mass SU2GaussianConeCoordinates.chartRate
    fun_prop
  apply (wider_gaussian_integrable.const_mul K).mono' hm.aestronglyMeasurable
  filter_upwards with Y
  have hbudget := budget_positive Y x y z
  have hp := Real.pow_div_factorial_le_exp (budget Y x y z/8)
    (show 0 ≤ budget Y x y z/8 from div_nonneg hbudget.le (by norm_num)) 3
  have hp' : (budget Y x y z)^3 ≤ 6*(8 : ℝ)^3*Real.exp (budget Y x y z/8) := by
    norm_num at hp
    nlinarith
  have he : Real.exp (budget Y x y z/8)*Real.exp (-mass Y/4)=
      Real.exp ((1+|x|+|y|+|z|)/8)*Real.exp (-mass Y/8) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    unfold budget
    ring
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (6*(8 : ℝ)^3*Real.exp (budget Y x y z/8))*Real.exp (-mass Y/4) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
    _ = K*Real.exp (-mass Y/8) := by rw [mul_assoc,he]; dsimp [K]; ring

end OperatorDerivativeRewrite.Foundation.FourCubeFullOddEnvelope
