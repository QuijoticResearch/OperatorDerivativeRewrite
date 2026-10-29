import Foundation.FourCubeMovingOddAction
import Mathlib.Analysis.Calculus.MeanValue

/-! Explicit cubic envelopes for the actual full-cell odd-action quotient. -/
noncomputable section
open Filter Set MeasureTheory
open scoped Topology Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.FourCubeOddEnvelope
open QuaternionSU2Representation SU2QuaternionOddWord SU2TraceHessianModel
open FourCubeMovingOddAction FourCubeHemisphereCoercivity FourCubeHaarLaplaceDensity
open FourCubeScaledBoundaryControl FourCubeMovingActionLimit FourCubeMovingBoundaryQuadratic
open OneSidedBlockIncidence
open FourCubePinnedSecondVariation FourCubePinnedHaar OneSidedBlockRank OneSidedCapComplex
attribute [local irreducible] edges upperFaces innerFaces

theorem triple_bound (u v w : Vector) (M : ℝ) (hM : 0 ≤ M)
    (hu : ∀ a,|u a| ≤ M) (hv : ∀ a,|v a| ≤ M) (hw : ∀ a,|w a| ≤ M) :
    |triple u v w| ≤ 6*M^3 := by
  let terms : Fin 6 → ℝ := ![u 0*v 1*w 2,-(u 0*v 2*w 1),-(u 1*v 0*w 2),
    u 1*v 2*w 0,u 2*v 0*w 1,-(u 2*v 1*w 0)]
  have he : triple u v w=∑ i : Fin 6,terms i := by
    simp [triple,terms,Fin.sum_univ_succ]
    ring
  have hm (a b c : Fin 3) : |u a*v b*w c| ≤ M^3 := by
    rw [abs_mul,abs_mul]
    calc
      _ ≤ M*M*M := by gcongr; exact hu a; exact hv b; exact hw c
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ ∑ i : Fin 6,|terms i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin 6,M^3 := by
      apply Finset.sum_le_sum
      intro i _
      fin_cases i
      · simpa [terms] using hm 0 1 2
      · simpa [terms] using hm 0 2 1
      · simpa [terms] using hm 1 0 2
      · simpa [terms] using hm 1 2 0
      · simpa [terms] using hm 2 0 1
      · simpa [terms] using hm 2 1 0
    _ = _ := by simp

theorem weightedCubic_bound (r : Fin 4 → ℝ) (v : Fin 4 → Vector) (M : ℝ) (hM : 0 ≤ M)
    (hr : ∀ i,|r i| ≤ 1) (hv : ∀ i a,|v i a| ≤ M) :
    |weightedCubic r v| ≤ 24*M^3 := by
  have hb (i j k l : Fin 4) : |r i*triple (v j) (v k) (v l)| ≤ 6*M^3 := by
    rw [abs_mul]
    calc
      _ ≤ 1*(6*M^3) := mul_le_mul (hr i) (triple_bound _ _ _ M hM (hv j) (hv k) (hv l))
        (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  unfold weightedCubic
  have h0 := abs_add_le (r 3*triple (v 0) (v 1) (v 2)) (r 2*triple (v 0) (v 1) (v 3))
  have h1 := abs_add_le (r 3*triple (v 0) (v 1) (v 2)+r 2*triple (v 0) (v 1) (v 3))
    (r 1*triple (v 0) (v 2) (v 3))
  have h2 := abs_add_le (r 3*triple (v 0) (v 1) (v 2)+r 2*triple (v 0) (v 1) (v 3)+
    r 1*triple (v 0) (v 2) (v 3)) (r 0*triple (v 1) (v 2) (v 3))
  linarith [hb 3 0 1 2,hb 2 0 1 3,hb 1 0 2 3,hb 0 1 2 3]

def budget (Y : Coordinates) (x y z : ℝ) : ℝ :=
  1+quadraticMass Y+|x|+|y|+|z|

theorem mass_nonneg (Y : Coordinates) : 0 ≤ quadraticMass Y := by
  rw [quadraticMass_sum_squares]
  exact Finset.sum_nonneg (fun e _ => Finset.sum_nonneg (fun a _ => sq_nonneg _))

theorem budget_positive (Y : Coordinates) (x y z : ℝ) : 0 < budget Y x y z := by
  unfold budget
  linarith [mass_nonneg Y,abs_nonneg x,abs_nonneg y,abs_nonneg z]

theorem coordinate_bound (Y : Coordinates) (x y z : ℝ) (e : OneSidedPinnedInterior.Free) (a : Fin 3) :
    |Y e a| ≤ budget Y x y z := by
  have h1 : (Y e a)^2 ≤ ∑ b : Fin 3,(Y e b)^2 :=
    Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have h2 : (∑ b : Fin 3,(Y e b)^2) ≤ quadraticMass Y := by
    rw [quadraticMass_sum_squares]
    exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun b _ => sq_nonneg _)) (Finset.mem_univ e)
  have hh := sq_abs (Y e a)
  unfold budget
  nlinarith [sq_nonneg (|Y e a|-1),mass_nonneg Y,abs_nonneg x,abs_nonneg y,abs_nonneg z]

theorem lifted_coordinate_bound (Y : Coordinates) (x y z : ℝ) (e : Interior) (a : Fin 3) :
    |liftVelocity Y e a| ≤ budget Y x y z := by
  by_cases hp : e=OneSidedPinnedInterior.pole
  · subst e
    rw [liftVelocity_pole]
    simpa using (budget_positive Y x y z).le
  · have he := congrFun (liftVelocity_free Y (⟨e,hp⟩ : OneSidedPinnedInterior.Free)) a
    rw [he]
    exact coordinate_bound Y x y z _ a

theorem chart_weight_bounds (u : SU2GaussianConeCoordinates.Triple) (t : ℝ) :
    0 ≤ SU2HemisphereJets.weight u t ∧ SU2HemisphereJets.weight u t ≤ 1 := by
  have hs := SU2HemisphereJets.sizeSq_nonneg u
  have hp : 0 < 1+t^2*SU2HemisphereJets.sizeSq u := by positivity
  have hsq := Real.sq_sqrt hp.le
  have hr := Real.sqrt_nonneg (1+t^2*SU2HemisphereJets.sizeSq u)
  have hge : 1 ≤ Real.sqrt (1+t^2*SU2HemisphereJets.sizeSq u) := by nlinarith [sq_nonneg t]
  exact ⟨by unfold SU2HemisphereJets.weight; positivity,
    (inv_le_one₀ (Real.sqrt_pos.mpr hp)).mpr hge⟩

theorem chart_component_bound (u : SU2GaussianConeCoordinates.Triple) (t : ℝ) (ht : t ≠ 0)
    (a : Fin 3) : |imagVector (recover (SU2HemisphereJets.curve u t)) a/t| ≤ |u a| := by
  have he : recover (SU2HemisphereJets.curve u t)=
      SU2HemisphereJets.weight u t • SU2HemisphereChart.rawPoint (t • u) := by
    rw [SU2HemisphereJets.curve,SU2HemisphereChart.recover_chart,SU2HemisphereJets.radius_smul]
    rfl
  have hc : imagVector (recover (SU2HemisphereJets.curve u t)) a/t=
      SU2HemisphereJets.weight u t*u a := by
    rw [he]
    fin_cases a <;> simp [imagVector,SU2HemisphereChart.rawPoint,Pi.smul_apply,smul_eq_mul] <;>
      field_simp [ht] <;> ring
  rw [hc,abs_mul,abs_of_nonneg (chart_weight_bounds u t).1]
  exact mul_le_of_le_one_left (abs_nonneg _) (chart_weight_bounds u t).2

theorem axis_component_bound (k : Fin 3) (r t : ℝ) (ht : t ≠ 0) (a : Fin 3) :
    |imagVector (recover (SU2JointPlaquetteCubic.axis k (t*r) : M2)) a/t| ≤ |r| := by
  have he : recover (SU2JointPlaquetteCubic.axis k (t*r) : M2)=SU2JointPlaquetteCubic.axisRaw k (t*r) :=
    recover_repr _
  have hs : |Real.sin (t*r)/t| ≤ |r| := by
    rw [abs_div]
    apply (div_le_iff₀ (abs_pos.mpr ht)).mpr
    simpa [abs_mul,mul_comm] using (Real.abs_sin_le_abs (x := t*r))
  rw [he]
  fin_cases k <;> fin_cases a <;> simpa [imagVector,SU2JointPlaquetteCubic.axisRaw] using
    (show |Real.sin (t*r)/t| ≤ |r| from hs) <;> positivity

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
    have he : (links Y x y z t (.inl e) : M2)=SU2HemisphereJets.curve (liftVelocity Y e) t :=
      (FourCubeMovingBoundaryQuadratic.ratio_coordinate_actual Y t e).symm
    rw [he]
    exact (chart_component_bound _ t ht a).trans (lifted_coordinate_bound Y x y z e a)
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
    |(movingRay Y x y z t-movingRay Y x y z (-t))/(2*t^3)| ≤ 1728*(budget Y x y z)^3 := by
  rw [movingRay_rows,movingRay_rows,← Finset.sum_sub_distrib,Finset.sum_div]
  calc
    _ ≤ ∑ p : FullFace,|(wordAction (factors (links Y x y z t) p)-
        wordAction (factors (links Y x y z (-t)) p))/(2*t^3)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : FullFace,24*(budget Y x y z)^3 :=
      Finset.sum_le_sum (fun p _ => face_odd_bound Y x y z t ht p)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,fullFace_card,nsmul_eq_mul,Nat.cast_ofNat]; ring

theorem exponential_difference_bound (u v R : ℝ) (hu : u ≤ R) (hv : v ≤ R) :
    |Real.exp u-Real.exp v| ≤ Real.exp R*|u-v| := by
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (f := Real.exp) (s := Iic R)
    (fun a _ => (Real.hasDerivAt_exp a).differentiableAt)
    (fun a ha => by simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using
      Real.exp_le_exp.mpr ha) (convex_Iic R) hv hu
  simpa only [Real.norm_eq_abs] using hh

theorem cutoff_neg (t : ℝ) (Y : Coordinates) : Y∈scaledCutoff (-t) ↔ Y∈scaledCutoff t := by
  have he (e : OneSidedPinnedInterior.Free) : SU2GaussianConeCoordinates.chartRate ((-t) • Y e)=
      SU2GaussianConeCoordinates.chartRate (t • Y e) := by
    simp [SU2GaussianConeCoordinates.chartRate,Pi.smul_apply,smul_eq_mul]
  change (∀ e,SU2GaussianConeCoordinates.chartRate ((-t) • Y e) ≤ 2) ↔ _
  simp only [he]
  rfl

theorem scaled_exponent_bound (Y : Coordinates) (x y z t : ℝ) (ht : t ≠ 0)
    (hY : Y∈scaledCutoff t) :
    -movingRay Y x y z t/t^2 ≤ 216*(x^2+y^2+z^2)-quadraticMass Y/1116 := by
  have hβ : 0 ≤ 1/t^2 := by positivity
  have hc : (1/t^2)*t^2=1 := by field_simp
  have hh := scaled_action_lower (1/t^2) t hβ hc (movingBoundary t x y z) _
    (scaled_boundaryCost (1/t^2) t hβ hc x y z) Y hY
  change quadraticMass Y/1116-216*(x^2+y^2+z^2) ≤ (1/t^2)*movingRay Y x y z t at hh
  rw [div_mul_eq_mul_div,one_mul] at hh
  rw [neg_div]
  linarith

theorem actual_boltzmann_odd_bound (Y : Coordinates) (x y z t : ℝ) (ht : t ≠ 0)
    (hY : Y∈scaledCutoff t) :
    |(Real.exp (-movingRay Y x y z t/t^2)-Real.exp (-movingRay Y x y z (-t)/t^2))/(2*t)| ≤
      (1728*(budget Y x y z)^3*Real.exp (216*(x^2+y^2+z^2)))*Real.exp (-quadraticMass Y/1116) := by
  let R := 216*(x^2+y^2+z^2)-quadraticMass Y/1116
  have hp : -movingRay Y x y z t/t^2 ≤ R := scaled_exponent_bound Y x y z t ht hY
  have hm : -movingRay Y x y z (-t)/t^2 ≤ R := by
    simpa only [neg_sq] using scaled_exponent_bound Y x y z (-t) (neg_ne_zero.mpr ht) ((cutoff_neg t Y).mpr hY)
  have hh := exponential_difference_bound _ _ R hp hm
  have hd : ((-movingRay Y x y z t/t^2)-(-movingRay Y x y z (-t)/t^2))/(2*t)=
      -((movingRay Y x y z t-movingRay Y x y z (-t))/(2*t^3)) := by
    field_simp [ht]
    ring
  have he : Real.exp R=Real.exp (216*(x^2+y^2+z^2))*Real.exp (-quadraticMass Y/1116) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [R]
    ring
  rw [abs_div]
  calc
    _ ≤ (Real.exp R*|(-movingRay Y x y z t/t^2)-(-movingRay Y x y z (-t)/t^2)|)/|2*t| :=
      div_le_div_of_nonneg_right hh (abs_nonneg _)
    _ = Real.exp R*|(movingRay Y x y z t-movingRay Y x y z (-t))/(2*t^3)| := by
      rw [mul_div_assoc,← abs_div,hd,abs_neg]
    _ ≤ Real.exp R*(1728*(budget Y x y z)^3) :=
      mul_le_mul_of_nonneg_left (actual_odd_bound Y x y z t ht) (Real.exp_pos _).le
    _ = _ := by rw [he]; ring

theorem wider_gaussian_integrable :
    Integrable (fun Y : Coordinates => Real.exp (-quadraticMass Y/2232)) := by
  have hs : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hh := broadened_gaussian_integrable.comp_smul (inv_ne_zero hs)
  convert! hh using 1
  funext Y
  rw [quadraticMass_smul,inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

theorem cubic_weight_integrable (x y z : ℝ) :
    Integrable (fun Y : Coordinates => (budget Y x y z)^3*Real.exp (-quadraticMass Y/1116)) := by
  let K := 6*(2232 : ℝ)^3*Real.exp ((1+|x|+|y|+|z|)/2232)
  have hm : Measurable (fun Y : Coordinates => (budget Y x y z)^3*Real.exp (-quadraticMass Y/1116)) := by
    unfold budget quadraticMass SU2GaussianConeCoordinates.chartRate
    fun_prop
  apply (wider_gaussian_integrable.const_mul K).mono' hm.aestronglyMeasurable
  filter_upwards with Y
  have hbudget := budget_positive Y x y z
  have hp := Real.pow_div_factorial_le_exp (budget Y x y z/2232)
    (show 0 ≤ budget Y x y z/2232 from div_nonneg hbudget.le (by norm_num)) 3
  have hp' : (budget Y x y z)^3 ≤ 6*(2232 : ℝ)^3*Real.exp (budget Y x y z/2232) := by
    norm_num at hp
    nlinarith
  have he : Real.exp (budget Y x y z/2232)*Real.exp (-quadraticMass Y/1116)=
      Real.exp ((1+|x|+|y|+|z|)/2232)*Real.exp (-quadraticMass Y/2232) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    unfold budget
    ring
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  calc
    _ ≤ (6*(2232 : ℝ)^3*Real.exp (budget Y x y z/2232))*Real.exp (-quadraticMass Y/1116) :=
      mul_le_mul_of_nonneg_right hp' (Real.exp_pos _).le
    _ = K*Real.exp (-quadraticMass Y/2232) := by rw [mul_assoc,he]; dsimp [K]; ring
end OperatorDerivativeRewrite.Foundation.FourCubeOddEnvelope
