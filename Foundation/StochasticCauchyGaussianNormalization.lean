import Foundation.GaussianCore
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Actual independent two-coordinate Gaussian marginals for the stochastic
Cauchy source audit. A terminal marginal is not a constructed Brownian process. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyGaussianNormalization

abbrev law (v : ℝ≥0) : Measure (ℝ × ℝ) := (gaussianReal 0 v).prod (gaussianReal 0 v)

def z (q : ℝ × ℝ) : ℂ := (q.1 : ℂ)+Complex.I*(q.2 : ℂ)
def exponential (q : ℝ × ℝ) : ℂ := Complex.exp (z q)

theorem z_measurable : Measurable z := by unfold z; fun_prop

def complexLaw (v : ℝ≥0) : Measure ℂ := (law v).map z

theorem complexLaw_probability (v : ℝ≥0) : IsProbabilityMeasure (complexLaw v) := by
  constructor
  rw [complexLaw,Measure.map_apply z_measurable MeasurableSet.univ]
  simp

theorem hasLaw_z (v : ℝ≥0) : HasLaw z (complexLaw v) (law v) :=
  ⟨z_measurable.aemeasurable,rfl⟩

theorem exponential_measurable : Measurable exponential := by unfold exponential z; fun_prop

theorem exponential_norm_sq (q : ℝ × ℝ) : ‖exponential q‖^2=Real.exp (2*q.1) := by
  simp only [exponential,Complex.norm_exp,z,Complex.add_re,Complex.ofReal_re,
    Complex.mul_re,Complex.I_re,Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,
    sub_zero,add_zero]
  rw [← Real.exp_nat_mul]
  norm_num

theorem exponential_norm_integrable (v : ℝ≥0) :
    Integrable (fun q => ‖exponential q‖^2) (law v) := by
  simp only [exponential_norm_sq]
  exact (integrable_exp_mul_gaussianReal (μ := 0) (v := v) 2).comp_fst _

theorem exponential_memLp (v : ℝ≥0) : MemLp exponential 2 (law v) :=
  (memLp_two_iff_integrable_sq_norm exponential_measurable.aestronglyMeasurable).mpr
    (exponential_norm_integrable v)

theorem exponential_integrable (v : ℝ≥0) : Integrable exponential (law v) :=
  (exponential_memLp v).integrable (by norm_num)

private theorem real_exponential_mean (v : ℝ≥0) :
    (∫ x : ℝ, Complex.exp (x : ℂ) ∂gaussianReal 0 v)=Complex.exp ((v : ℂ)/2) := by
  simpa [complexMGF] using (complexMGF_id_gaussianReal (μ := 0) (v := v) (1 : ℂ))

private theorem imaginary_exponential_mean (v : ℝ≥0) :
    (∫ y : ℝ, Complex.exp (Complex.I*(y : ℂ)) ∂gaussianReal 0 v)=
      Complex.exp (-((v : ℂ)/2)) := by
  simpa [complexMGF,Complex.I_sq,neg_div] using
    (complexMGF_id_gaussianReal (μ := 0) (v := v) Complex.I)

theorem exponential_mean (v : ℝ≥0) : (∫ q, exponential q ∂law v)=1 := by
  rw [integral_prod _ (exponential_integrable v)]
  simp only [exponential,z,Complex.exp_add]
  simp_rw [integral_const_mul]
  rw [integral_mul_const,real_exponential_mean,imaginary_exponential_mean,
    ← Complex.exp_add,add_neg_cancel,Complex.exp_zero]

theorem exponential_second_moment (v : ℝ≥0) :
    (∫ q, ‖exponential q‖^2 ∂law v)=Real.exp (2*(v : ℝ)) := by
  simp only [exponential_norm_sq]
  rw [integral_prod _ ((integrable_exp_mul_gaussianReal (μ := 0) (v := v) 2).comp_fst _)]
  simp only [integral_const,probReal_univ,one_smul]
  have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) 2
  simp only [mgf,id_eq,zero_mul,zero_add] at h
  convert h using 1
  congr 1
  ring

def centeredEnergy (v : ℝ≥0) : ℝ := ∫ q, ‖exponential q-1‖^2 ∂law v

private theorem norm_sub_one (w : ℂ) : ‖w-1‖^2=‖w‖^2-2*w.re+1 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.one_re,Complex.one_im]
  ring

theorem centered_energy (v : ℝ≥0) : centeredEnergy v=Real.exp (2*(v : ℝ))-1 := by
  have hi := exponential_integrable v
  have hr : Integrable (fun q => (exponential q).re) (law v) := hi.re
  have hm : Integrable (fun q => 2*(exponential q).re) (law v) := hr.const_mul 2
  have hs : Integrable (fun q => ‖exponential q‖^2-2*(exponential q).re) (law v) :=
    (exponential_norm_integrable v).sub hm
  have hrmean : (∫ q, (exponential q).re ∂law v)=1 := by
    have h := Complex.reCLM.integral_comp_comm hi
    change (∫ q, (exponential q).re ∂law v)=(∫ q, exponential q ∂law v).re at h
    rw [exponential_mean] at h
    exact h
  unfold centeredEnergy
  simp only [norm_sub_one]
  rw [integral_add hs (integrable_const 1),
    integral_sub (exponential_norm_integrable v) hm,integral_const_mul,
    hrmean,exponential_second_moment]
  simp
  ring

theorem z_norm_sq (q : ℝ × ℝ) : ‖z q‖^2=q.1^2+q.2^2 := by
  simp [z,Complex.sq_norm,Complex.normSq_apply]
  ring

private theorem coordinate_square_integrable (v : ℝ≥0) :
    Integrable (fun x : ℝ => x^2) (gaussianReal 0 v) :=
  (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).mp
    (memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp))

private theorem coordinate_second (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 v)=(v : ℝ) := by
  have hm : MemLp id 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal' (μ := 0) (v := v) 2 (by simp)
  have h := variance_eq_sub hm
  rw [variance_id_gaussianReal] at h
  change (v : ℝ)=(∫ x : ℝ, x^2 ∂gaussianReal 0 v)-(∫ x : ℝ, x ∂gaussianReal 0 v)^2 at h
  rw [integral_id_gaussianReal] at h
  simpa using h.symm

theorem z_norm_integrable (v : ℝ≥0) : Integrable (fun q => ‖z q‖^2) (law v) := by
  simp only [z_norm_sq]
  exact ((coordinate_square_integrable v).comp_fst _).add
    ((coordinate_square_integrable v).comp_snd _)

theorem z_second_moment (v : ℝ≥0) : (∫ q, ‖z q‖^2 ∂law v)=2*(v : ℝ) := by
  simp only [z_norm_sq]
  rw [integral_add ((coordinate_square_integrable v).comp_fst _)
    ((coordinate_square_integrable v).comp_snd _),
    integral_prod _ ((coordinate_square_integrable v).comp_fst _),
    integral_prod _ ((coordinate_square_integrable v).comp_snd _)]
  simp [coordinate_second]
  ring

def manuscriptEnergy (T : ℝ≥0) : ℝ := (Real.exp (2*(T : ℝ))-1)/2

theorem normalized_energy (T : ℝ≥0) : centeredEnergy (T/2)=Real.exp (T : ℝ)-1 := by
  rw [centered_energy]
  push_cast
  ring_nf

theorem normalized_error (T : ℝ≥0) :
    manuscriptEnergy T-centeredEnergy (T/2)=(Real.exp (T : ℝ)-1)^2/2 := by
  rw [normalized_energy]
  unfold manuscriptEnergy
  have h : Real.exp (2*(T : ℝ))=(Real.exp (T : ℝ))^2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h]
  ring

/-- The manuscript's exponential energy is false under its stated normalized
complex Gaussian convention, at EVERY positive time. -/
theorem normalized_counter (T : ℝ≥0) (hT : 0 < T) :
    centeredEnergy (T/2)<manuscriptEnergy T := by
  have hp : 1<Real.exp (T : ℝ) := Real.one_lt_exp_iff.mpr hT
  have h := normalized_error T
  nlinarith [sq_pos_of_pos (sub_pos.mpr hp)]

theorem unnormalized_energy (T : ℝ≥0) : centeredEnergy T=2*manuscriptEnergy T := by
  rw [centered_energy]
  unfold manuscriptEnergy
  ring

theorem unnormalized_counter (T : ℝ≥0) (hT : 0 < T) :
    manuscriptEnergy T<centeredEnergy T := by
  have hp : 1<Real.exp (2*(T : ℝ)) :=
    Real.one_lt_exp_iff.mpr (by exact mul_pos (by norm_num) hT)
  rw [centered_energy]
  unfold manuscriptEnergy
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℂ}

/-- Exact transfer to any actual random variable with the stated marginal law.
No Brownian process or filtration is assumed to have been constructed here. -/
theorem exponential_mean_of_hasLaw (v : ℝ≥0) (hZ : HasLaw Z (complexLaw v) μ) :
    (∫ ω, Complex.exp (Z ω) ∂μ)=1 := by
  have h1 := hZ.integral_comp (f := Complex.exp) (by fun_prop)
  have h2 := (hasLaw_z v).integral_comp (f := Complex.exp) (by fun_prop)
  exact h1.trans (h2.symm.trans (exponential_mean v))

theorem centered_energy_of_hasLaw (v : ℝ≥0) (hZ : HasLaw Z (complexLaw v) μ) :
    (∫ ω, ‖Complex.exp (Z ω)-1‖^2 ∂μ)=Real.exp (2*(v : ℝ))-1 := by
  have h1 := hZ.integral_comp (f := fun w : ℂ => ‖Complex.exp w-1‖^2) (by fun_prop)
  have h2 := (hasLaw_z v).integral_comp (f := fun w : ℂ => ‖Complex.exp w-1‖^2) (by fun_prop)
  exact h1.trans (h2.symm.trans (centered_energy v))

end OperatorDerivativeRewrite.Foundation.StochasticCauchyGaussianNormalization
