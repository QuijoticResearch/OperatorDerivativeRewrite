import Foundation.IBMConstructedSources

/-! Finite-horizon square integrability of actual smooth IBM and derivative
evaluations. This proves a time/probability domain, not adapted stochastic integration. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace OperatorDerivativeRewrite.Foundation.IBMFiniteHorizonEvaluation
open InfiniteGaussian IBMSourceLaws IBMConstructedSources IBMPointwiseEvaluation
open IBMJointMollifierGaussian IBMRandomDerivativeIntegrability IBMContinuousScenery
attribute [local instance] FractionalSpectralKernel.spectralSpace_secondCountable
attribute [local irreducible] IBMDyadicExtension.field
attribute [local irreducible] IBMConstructedSources.mollifiedValue

theorem mollifiedValue_sq_integral (n : ℕ) (i : Fin 3) (t : ℝ≥0) :
    (∫ ω, (mollifiedValue n i t ω)^2 ∂jointMeasure) =
      ∫ ωY, ‖randomKernelClass (derivativeKernel n i) t ωY‖^2 ∂gaussianProduct := by
  have he : (∫ ω, (mollifiedValue n i t ω)^2 ∂jointMeasure) =
      ∫ ω, (value n i t ω)^2 ∂jointMeasure := by
    apply integral_congr_ae
    filter_upwards [mollifiedValue_ae_original n i t] with ω hω
    rw [hω]
  rw [he]
  have hi : Integrable (fun ω => (value n i t ω)^2) jointMeasure :=
    (memLp_two_iff_integrable_sq (value_measurable n i t).aestronglyMeasurable).mp
      (value_memLp n i t)
  change (∫ ω, (value n i t ω)^2 ∂gaussianProduct.prod gaussianProduct) = _
  rw [integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun ωY => by
    simpa only [value, randomKernelClass] using
      field_sq_integral n i |GaussianTimeProcess.process t ωY|

theorem mollifiedValue_sq_le (n : ℕ) (i : Fin 3) (t : ℝ≥0) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ z, R < |z| → derivativeKernel n i z = 0) :
    (∫ ω, (mollifiedValue n i t ω)^2 ∂jointMeasure) ≤
      (kernelMass R (derivativeKernel n i))^2 * (1+(t : ℝ)+R) := by
  rw [mollifiedValue_sq_integral]
  let A : ℝ := kernelMass R (derivativeKernel n i)
  have hi := (memLp_two_iff_integrable_sq_norm
    (randomDerivativeClass_memLp n i t).aestronglyMeasurable).mp (randomDerivativeClass_memLp n i t)
  have hs : Integrable (fun ω => (GaussianTimeProcess.process t ω)^2) gaussianProduct := by
    simpa only [pow_two] using GaussianTimeProcess.process_product_integrable t t
  have hm : Integrable (fun ω => A^2*(1+(GaussianTimeProcess.process t ω)^2+R)) gaussianProduct :=
    ((integrable_const (1 : ℝ)).add hs |>.add (integrable_const R)).const_mul _
  have hb : (∫ ωY, ‖randomKernelClass (derivativeKernel n i) t ωY‖^2 ∂gaussianProduct) ≤
      ∫ ω, A^2*(1+(GaussianTimeProcess.process t ω)^2+R) ∂gaussianProduct := by
    apply integral_mono hi hm
    intro ω
    have h := wholeLineScenery_norm_sq_le (IBMDyadicExtension.derivativeKernel_regular n i).2.continuous
      hR hsupp |GaussianTimeProcess.process t ω|
    simp only [abs_abs] at h
    have ha : |GaussianTimeProcess.process t ω| ≤ 1+(GaussianTimeProcess.process t ω)^2 := by
      nlinarith [sq_nonneg (|GaussianTimeProcess.process t ω|-1),
        sq_abs (GaussianTimeProcess.process t ω)]
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg A))
  convert hb using 1
  rw [integral_const_mul]
  change _ = A^2 * (∫ ω, ((fun _ : SampleSpace => (1 : ℝ)) +
    (fun ω : SampleSpace => (GaussianTimeProcess.process t ω)^2) +
    (fun _ : SampleSpace => R) : SampleSpace → ℝ) ω ∂gaussianProduct)
  simp only [Pi.add_apply]
  have he1 : (∫ ω, 1+(GaussianTimeProcess.process t ω)^2+R ∂gaussianProduct) =
      (∫ ω, 1+(GaussianTimeProcess.process t ω)^2 ∂gaussianProduct) +
        (∫ _ω : SampleSpace, R ∂gaussianProduct) := by
    simpa only [Pi.add_apply] using
      integral_add ((integrable_const (1 : ℝ)).add hs) (integrable_const R)
  have he2 : (∫ ω, 1+(GaussianTimeProcess.process t ω)^2 ∂gaussianProduct) =
      (∫ _ω : SampleSpace, (1 : ℝ) ∂gaussianProduct) +
        (∫ ω, (GaussianTimeProcess.process t ω)^2 ∂gaussianProduct) := by
    simpa only [Pi.add_apply] using integral_add (integrable_const (1 : ℝ)) hs
  rw [he1, he2]
  have he : (∫ ω, (GaussianTimeProcess.process t ω)^2 ∂gaussianProduct) = (t : ℝ) := by
    simpa only [pow_two, min_self] using GaussianTimeProcess.process_product_integral t t
  rw [he]
  simp only [integral_const, probReal_univ, one_smul]
  rfl

theorem horizon_square_integrable_of_support (n : ℕ) (i : Fin 3) (T R : ℝ)
    (hR : 0 ≤ R) (hsupp : ∀ z, R < |z| → derivativeKernel n i z = 0) :
    Integrable (fun p : ℝ × JointSample => (mollifiedValue n i (Real.toNNReal p.1) p.2)^2)
      ((volume.restrict (Set.Ioc 0 T)).prod jointMeasure) := by
  have hm : Measurable (fun p : ℝ × JointSample => mollifiedValue n i (Real.toNNReal p.1) p.2) :=
    (mollifiedValue_jointly_measurable n i).comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
  have hmsq := hm.pow_const 2
  apply (integrable_prod_iff hmsq.aestronglyMeasurable).mpr
  constructor
  · apply Eventually.of_forall
    intro r
    have hmr : Measurable (mollifiedValue n i (Real.toNNReal r)) :=
      (mollifiedValue_jointly_measurable n i).comp (measurable_const.prodMk measurable_id)
    exact (memLp_two_iff_integrable_sq hmr.aestronglyMeasurable).mp
      (mollifiedValue_memLp n i (Real.toNNReal r))
  · let C := (kernelMass R (derivativeKernel n i))^2 * (1+T+R)
    apply Integrable.mono' (integrable_const C)
      hmsq.aestronglyMeasurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have he : (∫ ω, ‖(mollifiedValue n i (Real.toNNReal r) ω)^2‖ ∂jointMeasure) =
        ∫ ω, (mollifiedValue n i (Real.toNNReal r) ω)^2 ∂jointMeasure := by
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
    rw [Real.norm_eq_abs, he, abs_of_nonneg (integral_nonneg fun ω => sq_nonneg _)]
    have hb := mollifiedValue_sq_le n i (Real.toNNReal r) R hR hsupp
    rw [Real.coe_toNNReal r hr.1.le] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (by linarith [hr.2]) (sq_nonneg _))

/-- U,V,W at the constructed continuous clock genuinely belong to the square
integrable time/probability domain on every finite horizon. No support radius
or stochastic path hypothesis remains in this public application theorem. -/
theorem horizon_square_integrable (n : ℕ) (i : Fin 3) (T : ℝ) :
    Integrable (fun p : ℝ × JointSample => (mollifiedValue n i (Real.toNNReal p.1) p.2)^2)
      ((volume.restrict (Set.Ioc 0 T)).prod jointMeasure) := by
  have hc := (IBMDyadicExtension.derivativeKernel_regular n i).1
  obtain ⟨M, hM⟩ := hc.isCompact.exists_bound_of_continuousOn continuous_id.continuousOn
  let R := max M 0 + 1
  apply horizon_square_integrable_of_support n i T R (by dsimp [R]; positivity)
  intro z hz
  by_contra hne
  have hh := hM z (subset_closure hne)
  have hR : M < R := by dsimp [R]; linarith [le_max_left M 0]
  exact (not_lt_of_ge (by simpa only [Real.norm_eq_abs, id_eq] using hh)) (hR.trans hz)

def horizonValue (n : ℕ) (i : Fin 3) (p : ℝ × JointSample) : ℝ :=
  mollifiedValue n i (Real.toNNReal p.1) p.2

theorem horizonValue_measurable (n : ℕ) (i : Fin 3) : Measurable (horizonValue n i) :=
  (mollifiedValue_jointly_measurable n i).comp
    ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)

/-- Actual nonlinear first coefficient in the square-integrable time/source
domain for bounded test derivative. Adaptedness is still a separate obligation. -/
theorem firstCoefficient_horizon_square_integrable (f₁ : ℝ → ℝ) (hf₁ : Continuous f₁)
    (C a T : ℝ) (hbound : ∀ z, |f₁ z| ≤ C) (n : ℕ) :
    Integrable (fun p => (f₁ (a + horizonValue n 0 p) * horizonValue n 1 p)^2)
      ((volume.restrict (Set.Ioc 0 T)).prod jointMeasure) := by
  have hm : Measurable (fun p => f₁ (a+horizonValue n 0 p) * horizonValue n 1 p) :=
    (hf₁.measurable.comp (measurable_const.add (horizonValue_measurable n 0))).mul
      (horizonValue_measurable n 1)
  apply Integrable.mono' ((horizon_square_integrable n 1 T).const_mul (C^2))
    (hm.pow_const 2).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  change |(f₁ (a+horizonValue n 0 p)*horizonValue n 1 p)^2| ≤ C^2*(horizonValue n 1 p)^2
  rw [abs_of_nonneg (sq_nonneg _), mul_pow]
  have hf : (f₁ (a+horizonValue n 0 p))^2 ≤ C^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hbound (a+horizonValue n 0 p)) 2
  exact mul_le_mul_of_nonneg_right hf (sq_nonneg _)

theorem secondCoefficient_horizon_integrable (f₁ f₂ : ℝ → ℝ)
    (hf₁ : Continuous f₁) (hf₂ : Continuous f₂) (C₁ C₂ a T : ℝ)
    (hbound₁ : ∀ z, |f₁ z| ≤ C₁) (hbound₂ : ∀ z, |f₂ z| ≤ C₂) (n : ℕ) :
    Integrable (fun p => f₂ (a+horizonValue n 0 p)*(horizonValue n 1 p)^2 +
      f₁ (a+horizonValue n 0 p)*horizonValue n 2 p)
      ((volume.restrict (Set.Ioc 0 T)).prod jointMeasure) := by
  have hterm1 : Integrable (fun p => f₂ (a+horizonValue n 0 p)*(horizonValue n 1 p)^2)
      ((volume.restrict (Set.Ioc 0 T)).prod jointMeasure) := by
    apply Integrable.mono' ((horizon_square_integrable n 1 T).const_mul C₂)
      (((hf₂.measurable.comp (measurable_const.add (horizonValue_measurable n 0))).mul
        ((horizonValue_measurable n 1).pow_const 2)).aestronglyMeasurable)
    apply Eventually.of_forall
    intro p
    simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply, Function.comp_apply,
      abs_mul, abs_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right (hbound₂ _) (sq_nonneg _)
  have hC₁ : 0 ≤ C₁ := (abs_nonneg (f₁ 0)).trans (hbound₁ 0)
  have hterm2 : Integrable (fun p => f₁ (a+horizonValue n 0 p)*horizonValue n 2 p)
      ((volume.restrict (Set.Ioc 0 T)).prod jointMeasure) := by
    apply Integrable.mono' (((integrable_const (1 : ℝ)).add
      (horizon_square_integrable n 2 T)).const_mul C₁)
      (((hf₁.measurable.comp (measurable_const.add (horizonValue_measurable n 0))).mul
        (horizonValue_measurable n 2)).aestronglyMeasurable)
    apply Eventually.of_forall
    intro p
    simp only [Real.norm_eq_abs, Pi.mul_apply, Pi.add_apply, Function.comp_apply, abs_mul]
    calc
      _ ≤ C₁*|horizonValue n 2 p| := mul_le_mul_of_nonneg_right (hbound₁ _) (abs_nonneg _)
      _ ≤ C₁*(1+(horizonValue n 2 p)^2) := by
        apply mul_le_mul_of_nonneg_left _ hC₁
        nlinarith [sq_nonneg (|horizonValue n 2 p|-1), sq_abs (horizonValue n 2 p)]
  exact hterm1.add hterm2

/-- The actual selected coordinate retains the full closed source derivative,
with the original integrated Brownian Hilbert direction as its coefficient. -/
theorem field_closedSourceDerivative_graph (n : ℕ) (i : Fin 3) (r : ℝ) :
    ((field_memLp n i r).toLp (fun ω => IBMDyadicExtension.field n i ω r),
      Lp.const 2 gaussianProduct
        (SeparableHilbertEmbedding.hilbertEmbedding FractionalSpectralKernel.SpectralSpace
          (wholeLineDirection (derivativeKernel n i) r))) ∈
        InfiniteGaussian.closedCylindricalDerivative.graph := by
  rw [field_toLp_eq, wholeLineScenery_eq_sourceEmbedding]
  exact sourceDirection_closedDerivative_graph _

/-- Each actual random-clock section has the same verified closed scenery
source derivative. This is a section theorem, not a joint nonlinear or clock
Malliavin derivative theorem. -/
theorem value_section_closedSourceDerivative_graph (n : ℕ) (i : Fin 3)
    (t : ℝ≥0) (ωY : SampleSpace) :
    ((field_memLp n i |GaussianTimeProcess.process t ωY|).toLp
      (fun ωX => value n i t (ωX, ωY)),
      Lp.const 2 gaussianProduct
        (SeparableHilbertEmbedding.hilbertEmbedding FractionalSpectralKernel.SpectralSpace
          (wholeLineDirection (derivativeKernel n i) |GaussianTimeProcess.process t ωY|))) ∈
        InfiniteGaussian.closedCylindricalDerivative.graph :=
  field_closedSourceDerivative_graph n i |GaussianTimeProcess.process t ωY|

end OperatorDerivativeRewrite.Foundation.IBMFiniteHorizonEvaluation
