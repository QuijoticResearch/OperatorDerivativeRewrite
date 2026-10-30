import Foundation.CubeGaussianRadialRoot
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Actual nontrivial radial L2 eigenvectors of the normalized Wilson limit. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Quaternion Matrix Matrix.Norms.Operator
namespace OperatorDerivativeRewrite.Foundation.CubeGaussianRadialEigenvector
open QuaternionSU2Representation
open CubeGaussianModes CubeGaussianChannelGround CubeGaussianRootGround CubeChartAction
open CubeGaussianGroundEigenvector CubeGaussianKernelChannels CubeCompressedNormLimit
open CubeGaussianCoordinateMeasure CubeGaussianSchurBound CubeBoundaryChartL2
open CubeGaussianRadialChannel CubeGaussianRadialRoot SU2GaussianConeCoordinates SU2HemisphereJets
attribute [local irreducible] gaussianState CubeBoundaryHaarL2.limit

private theorem square_gaussian (i : Fin 5) (z : Triple) :
    (Real.exp (-width i*sizeSq z))^2=Real.exp (-(2*width i)*sizeSq z) := by
  rw [pow_two,← Real.exp_add]
  congr 1
  ring

theorem weighted_power_integrable (j : Fin 5) (a : Fin 3) (n : ℕ) :
    Integrable (fun x : Boundary => (x j a)^n*(gaussianState x)^2) := by
  classical
  let f (i : Fin 5) (z : Triple) :=
    (if i=j then (z a)^n else 1)*Real.exp (-(2*width i)*sizeSq z)
  have hi (i : Fin 5) : Integrable (f i) := by
    have hb : 0 < 2*width i := mul_pos (by norm_num) (width_positive i)
    by_cases h : i=j
    · simpa only [f,if_pos h] using CubeGaussianTripleMoment.coordinate_integrable _ hb a n
    · simpa only [f,if_neg h,one_mul] using CubeGaussianChannelGround.gaussian_integrable _ hb
  have h := Integrable.fintype_prod hi
  rw [← volume_pi] at h
  convert h using 1
  funext x
  change (x j a)^n*(gaussianState x)^2=
    ∏ i,(if i=j then (x i a)^n else 1)*Real.exp (-(2*width i)*sizeSq (x i))
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq',Finset.mem_univ,ite_true]
  simp_rw [← square_gaussian]
  rw [Finset.prod_pow]
  unfold gaussianState
  rfl

theorem radial_continuous (j : Fin 5) : Continuous (radial j) := by
  have hc : Continuous (fun x : Boundary => sizeSq (x j)) := by unfold sizeSq; fun_prop
  exact (hc.sub continuous_const).mul gaussianState_continuous

theorem radial_memLp (j : Fin 5) : MemLp (radial j) 2 (volume : Measure Boundary) := by
  apply (memLp_two_iff_integrable_sq (radial_continuous j).measurable.aestronglyMeasurable).mpr
  let D (x : Boundary) :=
    (6*((x j 0)^4+(x j 1)^4+(x j 2)^4)+2*(center j)^2)*(gaussianState x)^2
  have hD : Integrable D := by
    have h4 (a : Fin 3) := weighted_power_integrable j a 4
    have h0 := gaussianState_memLp.integrable_sq
    convert (((h4 0).add (h4 1)).add (h4 2)).const_mul 6 |>.add (h0.const_mul (2*(center j)^2)) using 1
    funext x
    simp only [D,Pi.add_apply]
    ring
  apply hD.mono' ((radial_continuous j).pow 2).measurable.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hb : (sizeSq (x j)-center j)^2 ≤ 6*((x j 0)^4+(x j 1)^4+(x j 2)^4)+2*(center j)^2 := by
    unfold sizeSq
    nlinarith [sq_nonneg ((x j 0)^2-(x j 1)^2),sq_nonneg ((x j 0)^2-(x j 2)^2),
      sq_nonneg ((x j 1)^2-(x j 2)^2),
      sq_nonneg ((x j 0)^2+(x j 1)^2+(x j 2)^2+center j)]
  change ((sizeSq (x j)-center j)*gaussianState x)^2 ≤ D x
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)

def actualRadial (j : Fin 5) (X : Boundary) : ℝ := radial j (analysis X)

theorem actualRadial_continuous (j : Fin 5) : Continuous (actualRadial j) :=
  (radial_continuous j).comp analysis_continuous

theorem actualRadial_memLp (j : Fin 5) : MemLp (actualRadial j) 2 (volume : Measure Boundary) := by
  apply (memLp_two_iff_integrable_sq (actualRadial_continuous j).measurable.aestronglyMeasurable).mpr
  apply (synthesis_integrable_iff (fun X => actualRadial j X^2)
    ((actualRadial_continuous j).pow 2).measurable).mp
  simpa only [actualRadial,analysis_synthesis] using (radial_memLp j).integrable_sq

def radialClass (j : Fin 5) : EuclideanL2 := (actualRadial_memLp j).toLp (actualRadial j)

theorem radialClass_coe (j : Fin 5) : radialClass j =ᵐ[volume] actualRadial j := MemLp.coeFn_toLp _

theorem radialClass_nonzero (j : Fin 5) : radialClass j ≠ 0 := by
  intro he
  have hz : actualRadial j =ᵐ[volume] (fun _ : Boundary => 0) := by
    have hc := radialClass_coe j
    rw [he] at hc
    exact hc.symm.trans (Lp.coeFn_zero ℝ 2 volume)
  have h := Measure.eq_of_ae_eq hz (actualRadial_continuous j) continuous_const
  have h0 := congrFun h (0 : Boundary)
  simp [actualRadial,radial,analysis,gaussianState,sizeSq] at h0
  have hp := center_positive j
  linarith

private theorem row_transform (j : Fin 5) (X y : Boundary) :
    CubeBoundaryHaarL2.limit (X,synthesis y)*actualRadial j (synthesis y)=
      constant*averagedRadial j (analysis X) y := by
  rw [actual_kernel_channels]
  simp only [actualRadial,analysis_synthesis,averagedRadial]
  ring

theorem actual_radial_row (j : Fin 5) (X : Boundary) :
    (∫ Y : Boundary,CubeBoundaryHaarL2.limit (X,Y)*actualRadial j Y)=
      (eigenvalue*(ratio j)^2)*actualRadial j X := by
  rw [coordinate_integral]
  simp_rw [row_transform]
  rw [integral_const_mul,averagedRadial_integral]
  unfold eigenvalue actualRadial
  ring

theorem actual_radial_row_integrable (j : Fin 5) (X : Boundary) :
    Integrable (fun Y : Boundary => CubeBoundaryHaarL2.limit (X,Y)*actualRadial j Y) := by
  have hi : Integrable (fun y : Boundary =>
      CubeBoundaryHaarL2.limit (X,synthesis y)*actualRadial j (synthesis y)) := by
    simpa only [row_transform] using (averagedRadial_integrable j (analysis X)).const_mul constant
  have h := coordinateEquiv.measurableEmbedding.integrable_map_iff
    (μ := (volume : Measure Boundary)) (g := fun Y : Boundary =>
      CubeBoundaryHaarL2.limit (X,Y)*actualRadial j Y)
  rw [show (coordinateEquiv : Boundary → Boundary)=synthesis from rfl,
    synthesis_map,integrable_smul_measure (by norm_num : (1/64:ENNReal)≠0)
      (by norm_num : (1/64:ENNReal)≠∞)] at h
  exact h.mpr hi

theorem actual_radial_eigenvector (j : Fin 5) :
    actualLimitOperator (radialClass j)=(eigenvalue*(ratio j)^2) • radialClass j := by
  apply ext_inner_right ℝ
  intro G
  rw [actualLimitOperator_integral_pairing,real_inner_smul_left,L2.inner_def,← integral_const_mul]
  have hrow (X : Boundary) :
      (∫ Y : Boundary,CubeBoundaryHaarL2.limit (X,Y)*radialClass j Y)=
        (eigenvalue*(ratio j)^2)*actualRadial j X := by
    rw [← actual_radial_row j X]
    apply integral_congr_ae
    filter_upwards [radialClass_coe j] with Y hY
    rw [hY]
  simp_rw [hrow]
  apply integral_congr_ae
  filter_upwards [radialClass_coe j] with X hX
  rw [hX,Real.inner_apply]
  ring

theorem normalized_radial_eigenvector (j : Fin 5) :
    CubeGroundNormLimit.normalizedLimitOperator (radialClass j)=(ratio j)^2 • radialClass j := by
  simp only [CubeGroundNormLimit.normalizedLimitOperator,smul_apply,
    actual_radial_eigenvector,smul_smul,norm_eq_eigenvalue]
  congr 1
  field_simp [eigenvalue_positive.ne']

theorem radial_ratio_bounds (j : Fin 5) : 0 < (ratio j)^2 ∧ (ratio j)^2 < 1 := by
  have hp := ratio_positive j
  have hl := ratio_lt_one j
  constructor <;> nlinarith

theorem radial_ground_orthogonal (j : Fin 5) : inner ℝ stateClass (radialClass j)=0 := by
  have h := ContinuousLinearMap.adjoint_inner_right actualLimitOperator stateClass (radialClass j)
  rw [actualLimitOperator_selfadjoint,actual_radial_eigenvector,actual_operator_eigenvector,
    real_inner_smul_right,real_inner_smul_left] at h
  have hn : eigenvalue*(ratio j)^2 ≠ eigenvalue := by
    have hb := (radial_ratio_bounds j).2
    nlinarith [eigenvalue_positive]
  have he : (eigenvalue*(ratio j)^2-eigenvalue)*inner ℝ stateClass (radialClass j)=0 := by
    nlinarith [h]
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hn)

theorem analysis_rotate (c : SU2) (X : Boundary) :
    analysis (fun i => SU2RootAdjoint.rotate c (X i))=
      fun i => SU2RootAdjoint.rotate c (analysis X i) := by
  have he : synthesis (fun i => SU2RootAdjoint.rotate c (analysis X i))=
      fun i => SU2RootAdjoint.rotate c (X i) := by
    funext i
    rw [← synthesis_rotate,synthesis_analysis]
  have h := congrArg analysis he
  rw [analysis_synthesis] at h
  exact h.symm

theorem actualRadial_root_invariant (j : Fin 5) (c : SU2) (X : Boundary) :
    actualRadial j (fun i => SU2RootAdjoint.rotate c (X i))=actualRadial j X := by
  unfold actualRadial
  rw [analysis_rotate]
  unfold radial gaussianState
  simp_rw [SU2RootAdjoint.rotate_sizeSq]

end OperatorDerivativeRewrite.Foundation.CubeGaussianRadialEigenvector
