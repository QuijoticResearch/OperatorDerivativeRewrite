import Foundation.CubeRootSchur

/-! Fixed-root Gaussian factorization of the actual Schur-reduced kernel coefficient. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeSchurIntegral
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2TraceHessianModel
open CubeChartAction CubeMixedForm CubeRootSchur CubeTemporalRootHaar
open CubeSlabSecondVariation CubeTemporalSchur
attribute [local irreducible] law

def temporalForm (Z : CubeRelativeChart.Field) : ℝ :=
  (∑ a : Fin 3,dotProduct (grad.mulVec (anchor (gaugeField Z) a))
    (grad.mulVec (anchor (gaugeField Z) a)))/8

def temporalConstant : ℝ := ∫ Z : CubeRelativeChart.Field,Real.exp (-temporalForm Z)

private theorem gauge_sub (Z S : CubeRelativeChart.Field) : gaugeField (Z-S)=gaugeField Z-gaugeField S := by
  funext v a
  by_cases hv : v=root
  · simp [gaugeField,hv]
  · fin_cases a <;> simp [gaugeField,hv,SU2HemisphereJets.frame] <;> ring
private theorem anchor_sub (G H : GaugeVelocity) (a : Fin 3) :
    anchor (G-H) a=anchor G a-anchor H a := by
  funext k
  simp only [anchor,Pi.sub_apply]
  ring

/-- Translation by the exact center leaves one boundary- and root-independent residual form. -/
theorem shifted_form (X Y : Boundary) (c : SU2) (Z : CubeRelativeChart.Field) :
    mixedForm X Y c Z=effective X Y c+temporalForm (Z-center X Y c) := by
  rw [CubeRootSchur.completed_square]
  congr 1
  unfold temporalForm remainder
  simp only [gauge_sub,anchor_sub,center_anchor]

theorem temporalForm_eq (Z : CubeRelativeChart.Field) : temporalForm Z=mixedForm 0 0 1 Z := by
  have hr : SU2RootAdjoint.rotate (1 : SU2) (0 : Triple)=0 := by
    simpa only [zero_smul] using SU2RootAdjoint.rotate_smul (1 : SU2) (0 : ℝ) (0 : Triple)
  have hf : SU2HemisphereJets.frame (0 : Triple)=(0 : Fin 3 → ℝ) := by
    ext a
    fin_cases a <;> simp [SU2HemisphereJets.frame]
  have hx : frameField (0 : Boundary)=0 := funext (fun _ => hf)
  have hy : rotatedField (1 : SU2) (0 : Boundary)=0 := by
    funext i
    change SU2HemisphereJets.frame (SU2RootAdjoint.rotate (1 : SU2) (0 : Triple))=0
    rw [hr,hf]
  have hd (a : Fin 3) : difference 0 0 (1 : SU2) a=0 := by
    ext j
    simp only [difference,hx,hy,Pi.zero_apply,sub_self]
  have hs : spatialCost 0=0 := by
    simp [spatialCost,hx,dotProduct]
  rw [CubeRootSchur.completed_square]
  unfold effective remainder temporalForm
  simp only [hs,hd,Matrix.mulVec_zero,dotProduct_zero,Finset.sum_const_zero,zero_div,
    add_zero,zero_add,sub_zero]

theorem temporalForm_continuous : Continuous temporalForm := by
  have hg (v : CubeTemporalSlab.SpatialVertex) (a : Fin 3) :
      Continuous (fun Z : CubeRelativeChart.Field => gaugeField Z v a) := by
    unfold gaugeField
    split_ifs
    · exact continuous_const
    · fin_cases a <;> unfold SU2HemisphereJets.frame <;> fun_prop
  have ha (k : Fin 7) (a : Fin 3) :
      Continuous (fun Z : CubeRelativeChart.Field => anchor (gaugeField Z) a k) :=
    (hg (vertexEnum k) a).sub (hg (![0,0,0] : CubeTemporalSlab.SpatialVertex) a)
  have hm (i : Fin 12) (a : Fin 3) : Continuous (fun Z : CubeRelativeChart.Field =>
      grad.mulVec (anchor (gaugeField Z) a) i) := by
    change Continuous (fun Z : CubeRelativeChart.Field => ∑ k : Fin 7,grad i k*anchor (gaugeField Z) a k)
    exact continuous_finset_sum Finset.univ (fun k _ =>
      (continuous_const : Continuous (fun _ : CubeRelativeChart.Field => grad i k)).mul (ha k a))
  exact (continuous_finset_sum _ (fun a _ =>
    continuous_finset_sum _ (fun i _ => (hm i a).mul (hm i a)))).div_const 8

theorem temporal_integrable : Integrable (fun Z : CubeRelativeChart.Field => Real.exp (-temporalForm Z)) := by
  apply CubeLocalKernel.gaussian_integrable.mono' (Real.continuous_exp.comp temporalForm_continuous.neg).aestronglyMeasurable
  filter_upwards with Z
  change ‖Real.exp (-temporalForm Z)‖ ≤ Real.exp (-CubeLocalKernel.mass Z/252)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  rw [temporalForm_eq]
  have h := mixedForm_lower 0 0 (1 : SU2) Z
  linarith

theorem temporalConstant_positive : 0 < temporalConstant := integral_exp_pos temporal_integrable

/-- Genuine fixed-root integration: the residual normalization is independent of both boundaries and c. -/
theorem fixed_root_integral (X Y : Boundary) (c : SU2) :
    (∫ Z : CubeRelativeChart.Field,Real.exp (-mixedForm X Y c Z))=
      Real.exp (-effective X Y c)*temporalConstant := by
  have he : (fun Z : CubeRelativeChart.Field => Real.exp (-mixedForm X Y c Z))=
      (fun Z => Real.exp (-effective X Y c)*Real.exp (-temporalForm (Z-center X Y c))) := by
    funext Z
    rw [shifted_form,neg_add,Real.exp_add]
  rw [he,integral_const_mul,integral_sub_right_eq_self
    (fun Z : CubeRelativeChart.Field => Real.exp (-temporalForm Z)) (center X Y c)]
  rfl


/-- Actual fixed-root integrability follows from the translated residual Gaussian. -/
theorem fixed_root_integrable (X Y : Boundary) (c : SU2) :
    Integrable (fun Z : CubeRelativeChart.Field => Real.exp (-mixedForm X Y c Z)) := by
  have hi := (temporal_integrable.comp_sub_right (center X Y c)).const_mul (Real.exp (-effective X Y c))
  convert hi using 1
  funext Z
  rw [shifted_form,neg_add,Real.exp_add]

private theorem joint_integrable (X Y : Boundary) :
    Integrable (fun p : SU2 × CubeRelativeChart.Field =>
      (chartDensity 0)^7*Real.exp (-mixedForm X Y p.1 p.2)) (law.prod volume) := by
  have he : (fun p : SU2 × CubeRelativeChart.Field =>
      (chartDensity 0)^7*Real.exp (-mixedForm X Y p.1 p.2))=CubeKernelLimit.limitDensity X Y :=
    funext (fun p => (CubeMixedForm.limitDensity_eq X Y p.1 p.2).symm)
  rw [he]
  exact CubeKernelLimit.limitDensity_integrable X Y

/-- The remaining genuine Haar-root integral has a verified integrable domain. -/
theorem root_weight_integrable (X Y : Boundary) :
    Integrable (fun c : SU2 => Real.exp (-effective X Y c)) law := by
  have hi := (joint_integrable X Y).integral_prod_left
  have he : (fun c : SU2 => ∫ Z : CubeRelativeChart.Field,
      (chartDensity 0)^7*Real.exp (-mixedForm X Y c Z))=
      (fun c => ((chartDensity 0)^7*temporalConstant)*Real.exp (-effective X Y c)) := by
    funext c
    rw [integral_const_mul,fixed_root_integral]
    ring
  rw [he] at hi
  have hC : 0 < (chartDensity 0)^7*temporalConstant :=
    mul_pos (pow_pos (FourCubeHaarLaplaceDensity.chartDensity_positive _) 7) temporalConstant_positive
  have hh := hi.const_mul (((chartDensity 0)^7*temporalConstant)⁻¹)
  convert hh using 1
  funext c
  simp only [← mul_assoc,inv_mul_cancel₀ hC.ne',one_mul]

/-- Actual limiting kernel coefficient after integrating all seven relative variables.
The outer Haar-root average remains and is not replaced by its value at1. -/
theorem kernel_tendsto (X Y : Boundary) :
    Tendsto (fun t : ℝ => CubeWilsonSlab.kernel (1/t^2) (boundaryRay X t) (boundaryRay Y t)/t^21)
      (𝓝[>] (0 : ℝ)) (𝓝 (((chartDensity 0)^7*temporalConstant)*
        (∫ c : SU2,Real.exp (-effective X Y c) ∂law))) := by
  have he : (∫ p : SU2 × CubeRelativeChart.Field,
      (chartDensity 0)^7*Real.exp (-mixedForm X Y p.1 p.2) ∂law.prod volume)=
      ((chartDensity 0)^7*temporalConstant)*(∫ c : SU2,Real.exp (-effective X Y c) ∂law) := by
    rw [integral_prod _ (joint_integrable X Y)]
    calc
      _ = ∫ c : SU2,(chartDensity 0)^7*(Real.exp (-effective X Y c)*temporalConstant) ∂law := by
        apply integral_congr_ae
        filter_upwards with c
        rw [integral_const_mul,fixed_root_integral]
      _ = ∫ c : SU2,((chartDensity 0)^7*temporalConstant)*Real.exp (-effective X Y c) ∂law := by
        apply integral_congr_ae
        filter_upwards with c
        ring
      _ = _ := integral_const_mul _ _
  simpa only [he] using CubeMixedForm.kernel_tendsto X Y

end OperatorDerivativeRewrite.Foundation.CubeSchurIntegral
