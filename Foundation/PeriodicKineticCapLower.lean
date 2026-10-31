import Foundation.SU2CapConvolutionLower
import Foundation.PeriodicPhysicalKineticReduction
/-! Actual192-link product-Haar cap averaging of the periodic kinetic kernel.
All coordinates and the actual Laplace normalization are retained. This is
an integration lower bound, not a pointwise gauge-average replacement. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.PeriodicKineticCapLower
open QuaternionSU2Representation FourCubePinnedCoercivity SU2HaarSmallCap
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicPhysicalKineticReduction CubeHaarUpper

def capBox (t : ℝ) : Set State := Set.univ.pi (fun _ => cap t)
theorem capBox_measurable (t : ℝ) : MeasurableSet (capBox t) :=
  MeasurableSet.univ_pi (fun _ => cap_measurable t)
theorem capBox_mass (t : ℝ) : boundaryHaar.real (capBox t)=(law.real (cap t))^192 := by
  change (boundaryHaar (capBox t)).toReal=(law (cap t)).toReal^192
  simp [boundaryHaar,capBox,Measure.pi_pi,Finset.prod_const,Finset.card_univ,ENNReal.toReal_pow]

private theorem product_integral {ι : Type*} [Fintype ι] (β t : ℝ) (C : ι → SU2) :
    (∫ h in Set.univ.pi (fun _ : ι => cap t),Real.exp (-β*(∑ i,defect (C i*h i)))
      ∂Measure.pi (fun _ => law))=
      ∏ i,∫ h in cap t,Real.exp (-β*defect (C i*h)) ∂law := by
  have he : (fun h : ι → SU2 => Real.exp (-β*(∑ i,defect (C i*h i))))=
      (fun h => ∏ i,Real.exp (-β*defect (C i*h i))) := by
    funext h
    rw [← Real.exp_sum]
    congr 1
    exact Finset.mul_sum _ _ _
  rw [he]
  change (∫ h,∏ i,Real.exp (-β*defect (C i*h i))
    ∂(Measure.pi (fun _ : ι => law)).restrict (Set.univ.pi (fun _ => cap t)))=_
  rw [Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (μ := fun _ : ι => law.restrict (cap t))
    (fun i h => Real.exp (-β*defect (C i*h)))

private theorem product_lower {ι : Type*} [Fintype ι] (β t : ℝ) (hb : 0 ≤ β) (C : ι → SU2) :
    (law.real (cap t))^(Fintype.card ι)*
      Real.exp (-β*((∑ i,defect (C i))+3*(Fintype.card ι : ℝ)*t^2)) ≤
      ∫ h in Set.univ.pi (fun _ : ι => cap t),Real.exp (-β*(∑ i,defect (C i*h i)))
        ∂Measure.pi (fun _ => law) := by
  rw [product_integral]
  have he : (∏ i,law.real (cap t)*Real.exp (-β*(defect (C i)+3*t^2)))=
      (law.real (cap t))^(Fintype.card ι)*
        Real.exp (-β*((∑ i,defect (C i))+3*(Fintype.card ι : ℝ)*t^2)) := by
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← Real.exp_sum]
    congr 2
    rw [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    ring
  rw [← he]
  apply Finset.prod_le_prod₀
  · intro i _
    exact mul_nonneg measureReal_nonneg (Real.exp_pos _).le
  · intro i _
    exact SU2CapConvolutionLower.cap_integral_lower β t hb (C i)

private theorem temporal_product (U V h : State) :
    temporalAction (U*h) V 1=∑ e,defect ((V e)⁻¹*U e*h e) := by
  unfold temporalAction
  apply Finset.sum_congr rfl
  intro e _
  unfold temporalWord defect
  simp only [Pi.mul_apply,Pi.one_apply,mul_one,inv_one]
  rw [SU2WilsonConvolution.halfTrace_mul_comm (U e*h e) (V e)⁻¹,mul_assoc]

theorem raw_cap_lower (β t : ℝ) (hb : 0 ≤ β) (U V : State) :
    (law.real (cap t))^192*Real.exp (-β*(temporalAction U V 1+576*t^2)) ≤
      ∫ h in capBox t,Real.exp (-β*temporalAction (U*h) V 1) ∂boundaryHaar := by
  have h := product_lower β t hb (fun e : SpatialEdge => (V e)⁻¹*U e)
  have hbase : temporalAction U V 1=∑ e,defect ((V e)⁻¹*U e) := by
    unfold temporalAction
    apply Finset.sum_congr rfl
    intro e _
    unfold temporalWord defect
    simp only [Pi.one_apply,mul_one,inv_one]
    rw [SU2WilsonConvolution.halfTrace_mul_comm]
  rw [edge_count,← hbase] at h
  norm_num only [Nat.cast_ofNat] at h
  have he : (fun h : State => Real.exp (-β*(∑ e,defect ((V e)⁻¹*U e*h e)) ))=
      (fun h => Real.exp (-β*temporalAction (U*h) V 1)) := by
    funext h
    rw [temporal_product]
  rw [he] at h
  simpa only [capBox,boundaryHaar] using h

theorem kinetic_cap_lower (β t : ℝ) (hb : 0 ≤ β) (U V : State) :
    (law.real (cap t))^192*Real.exp (-576*β*t^2)*kineticDensity β U V ≤
      ∫ h in capBox t,kineticDensity β (U*h) V ∂boundaryHaar := by
  have h := div_le_div_of_nonneg_right (raw_cap_lower β t hb U V)
    (pow_pos (laplace_pos β hb) 192).le
  rw [← integral_div] at h
  unfold kineticDensity
  have he : Real.exp (-β*(temporalAction U V 1+576*t^2))=
      Real.exp (-β*temporalAction U V 1)*Real.exp (-576*β*t^2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at h
  convert h using 1 <;> ring
/-- A genuine positive polynomial cap block for the actual kinetic density. -/
theorem kinetic_cap_power_lower (β t : ℝ) (hb : 0 ≤ β) (ht : 0 ≤ t) (h1 : t ≤ 1) (U V : State) :
    ((1/(4*Real.pi^2))*t^3)^192*Real.exp (-576*β*t^2)*kineticDensity β U V ≤
      ∫ h in capBox t,kineticDensity β (U*h) V ∂boundaryHaar := by
  have hp := pow_le_pow_left₀
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 1/(4*Real.pi^2)) (pow_nonneg ht 3))
    (mass_lower t ht h1) 192
  have hk : 0 ≤ kineticDensity β U V :=
    (div_pos (Real.exp_pos _) (pow_pos (laplace_pos β hb) _)).le
  have h := mul_le_mul_of_nonneg_right hp (mul_nonneg (Real.exp_pos (-576*β*t^2)).le hk)
  have h' : ((1/(4*Real.pi^2))*t^3)^192*Real.exp (-576*β*t^2)*kineticDensity β U V ≤
      (law.real (cap t))^192*Real.exp (-576*β*t^2)*kineticDensity β U V := by
    simpa only [mul_assoc] using h
  exact h'.trans (kinetic_cap_lower β t hb U V)
end OperatorDerivativeRewrite.Foundation.PeriodicKineticCapLower
