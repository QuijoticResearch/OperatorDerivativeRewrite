import Foundation.IBMPointwiseEvaluation
import Foundation.IBMSpatialFundamental
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Fubini identification of the actual continuous representative integrals. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology

namespace OperatorDerivativeRewrite.Foundation.IBMPathwiseFundamental
open InfiniteGaussian IBMJointMollifierGaussian IBMDyadicExtension
open IBMPointwiseEvaluation IBMContinuousScenery
attribute [local irreducible] IBMDyadicExtension.field

theorem class_continuous (n : ℕ) (i : Fin 3) :
    Continuous (wholeLineScenery (derivativeKernel n i)) :=
  wholeLineScenery_continuous (derivativeKernel_regular n i).1 (derivativeKernel_regular n i).2

theorem field_interval_product_sq_integrable (n : ℕ) (i : Fin 3) (a b : ℝ) :
    Integrable (fun p : ℝ × SampleSpace => (field n i p.2 p.1)^2)
      ((volume.restrict (Set.Ioc a b)).prod gaussianProduct) := by
  apply (integrable_prod_iff ((field_jointly_measurable n i).pow_const 2).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun r => field_sq_integrable n i r
  · have hi : IntegrableOn (fun r => ‖wholeLineScenery (derivativeKernel n i) r‖^2)
        (Set.Icc a b) volume := ((class_continuous n i).norm.pow 2).integrableOn_Icc
    have he : (fun r => ∫ ω, ‖(field n i ω r)^2‖ ∂gaussianProduct) =
        fun r => ‖wholeLineScenery (derivativeKernel n i) r‖^2 := by
      funext r
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      exact field_sq_integral n i r
    rw [he]
    exact hi.mono_set Set.Ioc_subset_Icc_self

theorem field_interval_product_integrable (n : ℕ) (i : Fin 3) (a b : ℝ) :
    Integrable (fun p : ℝ × SampleSpace => field n i p.2 p.1)
      ((volume.restrict (Set.Ioc a b)).prod gaussianProduct) := by
  have hs := field_interval_product_sq_integrable n i a b
  apply Integrable.mono' ((integrable_const (1 : ℝ)).add hs)
    (field_jointly_measurable n i).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  change |field n i p.2 p.1| ≤ 1 + (field n i p.2 p.1)^2
  nlinarith [sq_nonneg (|field n i p.2 p.1|-1), sq_abs (field n i p.2 p.1)]

theorem field_setIntegral_ae (n : ℕ) (i : Fin 3) (a b : ℝ) :
    (fun ω => ∫ r in Set.Ioc a b, field n i ω r) =ᵐ[gaussianProduct]
      (∫ r in Set.Ioc a b, wholeLineScenery (derivativeKernel n i) r : GaussianL2) := by
  have hf := field_interval_product_integrable n i a b
  let H : GaussianL2 := ∫ r in Set.Ioc a b, wholeLineScenery (derivativeKernel n i) r
  have hF : IntegrableOn (wholeLineScenery (derivativeKernel n i)) (Set.Ioc a b) volume :=
    (class_continuous n i).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ hf.integral_prod_right
    ((Lp.memLp H).integrable (by norm_num))
  intro s hs _hsfin
  let v : GaussianL2 := indicatorConstLp 2 hs (measure_ne_top gaussianProduct s) (1 : ℝ)
  have pair (r : ℝ) : (∫ ω in s, field n i ω r ∂gaussianProduct) =
      inner ℝ v (wholeLineScenery (derivativeKernel n i) r) := by
    rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
    simp only [Real.inner_apply, one_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (field_coordinate_ae n i r)] with ω hω
    rw [hω, wholeLineScenery_eq_sourceEmbedding]
    rfl
  have hfs : Integrable (fun p : ℝ × SampleSpace => field n i p.2 p.1)
      ((volume.restrict (Set.Ioc a b)).prod (gaussianProduct.restrict s)) :=
    hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ ω in s, (∫ r in Set.Ioc a b, field n i ω r) ∂gaussianProduct) =
        ∫ r in Set.Ioc a b, ∫ ω in s, field n i ω r ∂gaussianProduct :=
      (integral_integral_swap hfs).symm
    _ = ∫ r in Set.Ioc a b, inner ℝ v (wholeLineScenery (derivativeKernel n i) r) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall pair
    _ = inner ℝ v H := (innerSL ℝ v).integral_comp_comm hF
    _ = ∫ ω in s, H ω ∂gaussianProduct := by
      rw [L2.inner_indicatorConstLp_eq_setIntegral_inner]
      simp only [Real.inner_apply, one_mul]

/-- Transfer of an actual Hilbert-class FTC identity to the constructed
representatives, at two fixed ordered endpoints. -/
theorem field_FTC_ae (n : ℕ) (i j : Fin 3) (a b : ℝ) (hab : a ≤ b)
    (hclass : (∫ r in a..b, wholeLineScenery (derivativeKernel n j) r) =
      wholeLineScenery (derivativeKernel n i) b -
        wholeLineScenery (derivativeKernel n i) a) :
    ∀ᵐ ω ∂gaussianProduct, (∫ r in a..b, field n j ω r) =
      field n i ω b - field n i ω a := by
  rw [intervalIntegral.integral_of_le hab] at hclass
  have h := field_setIntegral_ae n j a b
  rw [hclass] at h
  have he (r : ℝ) : (wholeLineScenery (derivativeKernel n i) r : SampleSpace → ℝ) =
      gaussianTriple n r i := by rw [wholeLineScenery_eq_sourceEmbedding]; rfl
  filter_upwards [h, Lp.coeFn_sub (wholeLineScenery (derivativeKernel n i) b)
    (wholeLineScenery (derivativeKernel n i) a),
    field_coordinate_ae n i a, field_coordinate_ae n i b] with ω hω hsub ha hb
  rw [intervalIntegral.integral_of_le hab, hω, hsub]
  simp only [he]
  rw [ha, hb]
  rfl

theorem field_primitive_ae (n : ℕ) (i j : Fin 3)
    (hclass : ∀ a b : ℝ, (∫ r in a..b, wholeLineScenery (derivativeKernel n j) r) =
      wholeLineScenery (derivativeKernel n i) b -
        wholeLineScenery (derivativeKernel n i) a) (x : ℝ) :
    ∀ᵐ ω ∂gaussianProduct, (∫ r in 0..x, field n j ω r) =
      field n i ω x - field n i ω 0 := by
  by_cases hx : 0 ≤ x
  · exact field_FTC_ae n i j 0 x hx (hclass 0 x)
  · filter_upwards [field_FTC_ae n i j x 0 (le_of_not_ge hx) (hclass x 0)] with ω hω
    rw [intervalIntegral.integral_symm, hω]
    ring

theorem concrete_class_FTC (n : ℕ) :
    (∀ a b : ℝ, (∫ r in a..b, wholeLineScenery (derivativeKernel n 1) r) =
      wholeLineScenery (derivativeKernel n 0) b - wholeLineScenery (derivativeKernel n 0) a) ∧
    (∀ a b : ℝ, (∫ r in a..b, wholeLineScenery (derivativeKernel n 2) r) =
      wholeLineScenery (derivativeKernel n 1) b - wholeLineScenery (derivativeKernel n 1) a) := by
  constructor
  · intro a b
    simpa [derivativeKernel] using (concreteMollifier_integral_derivatives n a b).1
  · intro a b
    simpa [derivativeKernel] using (concreteMollifier_integral_derivatives n a b).2

theorem field_primitive_hasDerivAt (n : ℕ) (i : Fin 3) (ω : SampleSpace) (x : ℝ) :
    HasDerivAt (fun u => ∫ r in 0..u, field n i ω r) (field n i ω x) x := by
  have hc := field_continuous n i ω
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- One full-measure event carries both pathwise derivative identities at
every real point and every mollifier scale. This is derived from the Bochner
identities by Fubini, a countable rational endpoint event and continuity. -/
theorem field_common_hasDerivAt :
    ∀ᵐ ω ∂gaussianProduct, ∀ n : ℕ, ∀ x : ℝ,
      HasDerivAt (field n 0 ω) (field n 1 ω x) x ∧
      HasDerivAt (field n 1 ω) (field n 2 ω x) x := by
  have hrat : ∀ᵐ ω ∂gaussianProduct, ∀ n : ℕ, ∀ q : ℚ,
      ((∫ r in 0..(q : ℝ), field n 1 ω r) = field n 0 ω q - field n 0 ω 0) ∧
      ((∫ r in 0..(q : ℝ), field n 2 ω r) = field n 1 ω q - field n 1 ω 0) := by
    simp only [ae_all_iff]
    intro n q
    exact (field_primitive_ae n 0 1 (concrete_class_FTC n).1 q).and
      (field_primitive_ae n 1 2 (concrete_class_FTC n).2 q)
  filter_upwards [hrat] with ω hω
  intro n x
  have equal (i j : Fin 3)
      (h : ∀ q : ℚ, (∫ r in 0..(q : ℝ), field n j ω r) =
        field n i ω q - field n i ω 0) :
      (fun u => ∫ r in 0..u, field n j ω r) =
        fun u => field n i ω u - field n i ω 0 := by
    apply Rat.denseRange_cast.equalizer
    · exact continuous_iff_continuousAt.mpr fun u =>
        (field_primitive_hasDerivAt n j ω u).continuousAt
    · exact (field_continuous n i ω).sub continuous_const
    · funext q; exact h q
  have hu := equal 0 1 (fun q => (hω n q).1)
  have hv := equal 1 2 (fun q => (hω n q).2)
  constructor
  · have h := field_primitive_hasDerivAt n 1 ω x
    rw [hu] at h
    simpa only [sub_add_cancel] using h.add_const (field n 0 ω 0)
  · have h := field_primitive_hasDerivAt n 2 ω x
    rw [hv] at h
    simpa only [sub_add_cancel] using h.add_const (field n 1 ω 0)

/-- The three constructed fields form a genuine C² scenery modification. -/
theorem field_common_contDiff_two :
    ∀ᵐ ω ∂gaussianProduct, ∀ n : ℕ, ContDiff ℝ 2 (field n 0 ω) := by
  filter_upwards [field_common_hasDerivAt] with ω hω
  intro n
  have hU : Differentiable ℝ (field n 0 ω) := fun x => (hω n x).1.differentiableAt
  have hV : Differentiable ℝ (field n 1 ω) := fun x => (hω n x).2.differentiableAt
  have heU : deriv (field n 0 ω) = field n 1 ω := funext fun x => (hω n x).1.deriv
  have heV : deriv (field n 1 ω) = field n 2 ω := funext fun x => (hω n x).2.deriv
  have hV1 : ContDiff ℝ 1 (field n 1 ω) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨hV, ?_⟩
    rw [heV]
    exact field_continuous n 2 ω
  change ContDiff ℝ ((1 : WithTop ENat)+1) (field n 0 ω)
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨hU, by norm_num, ?_⟩
  rw [heU]
  exact hV1

end OperatorDerivativeRewrite.Foundation.IBMPathwiseFundamental
