import Foundation.FourCubeConditionalRadial
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Actual conditional Haar free energy and its large-coupling response. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeConditionalResponse
open QuaternionSU2Representation SU2JointPlaquetteCubic
open FourCubeHaarParity FourCubeIntegratedCubic FourCubeConditionalAction FourCubeConditionalRadial

def triple (x y z : ℝ) : SU2 := axis 0 x*axis 1 y*axis 2 z
def radius (x y z : ℝ) : ℝ := stapleRadius (triple x y z)
def constantPart (x z : ℝ) : ℝ := 5+2*(1-Real.cos x)+2*(1-Real.cos z)

def conditionalPartition (β x y z : ℝ) : ℝ :=
  ∫ U, Real.exp (-β*cellAction x y z (singleState U)) ∂law

def conditionalFreeEnergy (β x y z : ℝ) : ℝ := -Real.log (conditionalPartition β x y z)

theorem conditionalPartition_formula (β x y z : ℝ) : conditionalPartition β x y z=
    Real.exp (-β*constantPart x z)*mgf halfTrace law (β*radius x y z) := by
  have he (U : SU2) : -β*cellAction x y z (singleState U)=
      -β*constantPart x z+β*(4*halfTrace U+halfTrace (U*triple x y z)) := by
    rw [conditional_action]
    unfold constantPart triple
    ring
  unfold conditionalPartition
  simp_rw [he,Real.exp_add]
  rw [integral_const_mul,radial_integral]
  rfl

theorem scalar_domain : integrableExpSet halfTrace law=Set.univ := by
  ext t
  simp only [Set.mem_univ,iff_true]
  exact BoundedExponentialTiltResponse.exponential_integrable law halfTrace halfTrace_measurable halfTrace_bound t

theorem scalar_interior (t : ℝ) : t∈interior (integrableExpSet halfTrace law) := by
  rw [scalar_domain,interior_univ]
  trivial

theorem scalar_partition_pos (t : ℝ) : 0<mgf halfTrace law t :=
  mgf_pos (BoundedExponentialTiltResponse.exponential_integrable law halfTrace halfTrace_measurable halfTrace_bound t)

theorem conditionalPartition_pos (β x y z : ℝ) : 0<conditionalPartition β x y z := by
  rw [conditionalPartition_formula]
  exact mul_pos (Real.exp_pos _) (scalar_partition_pos _)

theorem conditionalFreeEnergy_formula (β x y z : ℝ) : conditionalFreeEnergy β x y z=
    β*constantPart x z-cgf halfTrace law (β*radius x y z) := by
  rw [conditionalFreeEnergy,conditionalPartition_formula,
    Real.log_mul (Real.exp_ne_zero _) (scalar_partition_pos _).ne',Real.log_exp]
  unfold cgf
  ring

def mean (t : ℝ) : ℝ :=
  ∫ U, halfTrace U ∂BoundedExponentialTiltResponse.tiltedMeasure law halfTrace t

theorem cgf_hasDerivAt (t : ℝ) : HasDerivAt (cgf halfTrace law) (mean t) t := by
  have he : deriv (cgf halfTrace law) t=mean t := by
    unfold mean
    rw [deriv_cgf (scalar_interior t),BoundedExponentialTiltResponse.tilted_integral law
      halfTrace halfTrace halfTrace_measurable halfTrace_bound t]
    simp only [BoundedExponentialTiltResponse.expectation,BoundedExponentialTiltResponse.partition,
      BoundedExponentialTiltResponse.weighted,one_mul,mgf]
  have h := (analyticAt_cgf (scalar_interior t)).differentiableAt.hasDerivAt
  rwa [he] at h

theorem mean_differentiable : Differentiable ℝ mean := by
  have h2 : ContDiff ℝ 2 (cgf halfTrace law) :=
    contDiff_iff_contDiffAt.mpr (fun t => (analyticAt_cgf (scalar_interior t)).contDiffAt)
  have he : mean=deriv (cgf halfTrace law) := funext (fun t => (cgf_hasDerivAt t).deriv.symm)
  rw [he]
  exact h2.differentiable_deriv_two

theorem mean_tendsto_one : Tendsto mean atTop (𝓝 1) :=
  SU2OneWordLargeCoupling.positive_mean_tendsto_one

theorem radius_bounds (x y z : ℝ) : 3≤radius x y z ∧ radius x y z≤5 := stapleRadius_bounds _

theorem trace_triple_formula (x y z : ℝ) : halfTrace (triple x y z)=
    Real.cos x*Real.cos y*Real.cos z-Real.sin x*Real.sin y*Real.sin z := by
  have h := FourCubeWilsonCubic.triple_action x y z
  rw [SU2JointPlaquetteCubic.action_formula] at h
  unfold triple
  linarith

theorem radius_sqrt (x y z : ℝ) : radius x y z=Real.sqrt
    (17+8*(Real.cos x*Real.cos y*Real.cos z-Real.sin x*Real.sin y*Real.sin z)) := by
  rw [radius,stapleRadius_sqrt,trace_triple_formula]

theorem radius_zero : radius 0 0 0=5 := by
  rw [radius_sqrt]
  norm_num

theorem radicand_pos (x y z : ℝ) :
    0<17+8*(Real.cos x*Real.cos y*Real.cos z-Real.sin x*Real.sin y*Real.sin z) := by
  have h := (abs_le.mp (halfTrace_bound (triple x y z))).1
  rw [trace_triple_formula] at h
  linarith


theorem radius_ne_zero (x y z : ℝ) : radius x y z ≠ 0 := by
  have h := (radius_bounds x y z).1
  linarith

theorem radius_y_hasDerivAt (x z : ℝ) :
    HasDerivAt (fun y => radius x y z)
      (-4*(Real.sin x*Real.sin z)/radius x 0 z) 0 := by
  have ht : HasDerivAt
      (fun y => Real.cos x*Real.cos y*Real.cos z-Real.sin x*Real.sin y*Real.sin z)
      (-Real.sin x*Real.sin z) 0 := by
    convert (((Real.hasDerivAt_cos 0).const_mul (Real.cos x)).mul_const (Real.cos z)).sub
      (((Real.hasDerivAt_sin 0).const_mul (Real.sin x)).mul_const (Real.sin z)) using 1 <;> simp
  have hh := ((hasDerivAt_const (0 : ℝ) 17).add (ht.const_mul 8)).sqrt
    (ne_of_gt (radicand_pos x 0 z))
  simp only [zero_add] at hh
  change HasDerivAt (fun y => Real.sqrt
    (17+8*(Real.cos x*Real.cos y*Real.cos z-Real.sin x*Real.sin y*Real.sin z)))
    ((8*(-Real.sin x*Real.sin z))/(2*Real.sqrt
      (17+8*(Real.cos x*Real.cos 0*Real.cos z-Real.sin x*Real.sin 0*Real.sin z)))) 0 at hh
  simp_rw [← radius_sqrt] at hh
  convert hh using 1 <;> ring

theorem radius_x_differentiable (y z : ℝ) : Differentiable ℝ (fun x => radius x y z) := by
  intro x
  simp_rw [radius_sqrt]
  apply DifferentiableAt.sqrt
  · fun_prop
  · exact (radicand_pos x y z).ne'

theorem radius_z_differentiable (x y : ℝ) : Differentiable ℝ (fun z => radius x y z) := by
  intro z
  simp_rw [radius_sqrt]
  apply DifferentiableAt.sqrt
  · fun_prop
  · exact (radicand_pos x y z).ne'

def responseCoeff (β x z : ℝ) : ℝ :=
  4*β*mean (β*radius x 0 z)/radius x 0 z

theorem conditional_y_hasDerivAt (β x z : ℝ) :
    HasDerivAt (fun y => conditionalFreeEnergy β x y z)
      (responseCoeff β x z*Real.sin x*Real.sin z) 0 := by
  simp_rw [conditionalFreeEnergy_formula]
  have hh := (hasDerivAt_const (0 : ℝ) (β*constantPart x z)).sub
    ((cgf_hasDerivAt (β*radius x 0 z)).comp 0 ((radius_y_hasDerivAt x z).const_mul β))
  convert hh using 1
  · rfl
  · unfold responseCoeff
    ring

theorem responseCoeff_x_differentiable (β z : ℝ) :
    Differentiable ℝ (fun x => responseCoeff β x z) := by
  unfold responseCoeff
  exact ((mean_differentiable.comp ((radius_x_differentiable 0 z).const_mul β)).const_mul
    (4*β)).div (radius_x_differentiable 0 z) (fun x => radius_ne_zero x 0 z)

theorem responseCoeff_z_differentiable (β x : ℝ) :
    Differentiable ℝ (fun z => responseCoeff β x z) := by
  unfold responseCoeff
  exact ((mean_differentiable.comp ((radius_z_differentiable x 0).const_mul β)).const_mul
    (4*β)).div (radius_z_differentiable x 0) (fun z => radius_ne_zero x 0 z)

theorem conditional_mixed_hessian (β z : ℝ) :
    deriv (fun x => deriv (fun y => conditionalFreeEnergy β x y z) 0) 0 =
      responseCoeff β 0 z*Real.sin z := by
  simp_rw [(conditional_y_hasDerivAt β _ z).deriv]
  have hh := (((responseCoeff_x_differentiable β z).differentiableAt.hasDerivAt).mul
    (Real.hasDerivAt_sin 0)).mul_const (Real.sin z)
  simpa using hh.deriv

theorem conditional_mixed_cubic (β : ℝ) :
    deriv (fun z => deriv (fun x => deriv (fun y => conditionalFreeEnergy β x y z) 0) 0) 0 =
      4*β/5*mean (5*β) := by
  simp_rw [conditional_mixed_hessian]
  have hh := ((responseCoeff_z_differentiable β 0).differentiableAt.hasDerivAt).mul
    (Real.hasDerivAt_sin 0)
  have he := hh.deriv
  simp only [Real.sin_zero,Real.cos_zero,mul_zero,zero_mul,zero_add,mul_one] at he
  change deriv (fun z => responseCoeff β 0 z*Real.sin z) 0 = responseCoeff β 0 0 at he
  exact he.trans (by
    unfold responseCoeff
    rw [radius_zero]
    congr 1 <;> ring)

theorem conditional_mixed_cubic_normalized_limit :
    Tendsto (fun β =>
      deriv (fun z => deriv (fun x => deriv (fun y => conditionalFreeEnergy β x y z) 0) 0) 0 / β)
      atTop (𝓝 (4/5 : ℝ)) := by
  have hm := mean_tendsto_one.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ)<5))
  have hl := hm.const_mul (4/5 : ℝ)
  simp only [mul_one] at hl
  apply hl.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  rw [conditional_mixed_cubic]
  dsimp only [Function.comp_def,id_eq]
  field_simp
  <;> ring

end OperatorDerivativeRewrite.Foundation.FourCubeConditionalResponse
