import Foundation.IBMPhysicalDerivativeColumn

/-! Identify the actual physical first-derivative convolution kernel with
the translated scalar mollifier, using the existing L2 representative Fubini rule. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalDerivativeKernel
open GaussianTimeHilbert IBMPhysicalNoiseVectors IBMPhysicalNoiseCalculus
open IBMPhysicalDerivativeColumn

def translatedClass (ρ : ℝ → ℝ) (hc : Continuous ρ) (hs : HasCompactSupport ρ) (x : ℝ) : TimeHilbert :=
  ((hc.comp (continuous_const.sub continuous_id)).memLp_of_hasCompactSupport
    (hs.comp_homeomorph (Homeomorph.subLeft x))).toLp (fun w => ρ (x-w))

theorem translatedClass_coeFn (ρ : ℝ → ℝ) (hc : Continuous ρ) (hs : HasCompactSupport ρ) (x : ℝ) :
    translatedClass ρ hc hs x =ᵐ[volume] fun w => ρ (x-w) := MemLp.coeFn_toLp _

theorem derivative_eq_translated_of_bounds {ρ : ℝ → ℝ} (hf : ContDiff ℝ 1 ρ)
    (hs : HasCompactSupport ρ) (x A B C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ r, ‖deriv ρ (x-r)‖ ≤ C)
    (hsupp : ∀ r, r ∉ Icc A B → deriv ρ (x-r)=0) :
    convolutionKernel (deriv ρ) x = translatedClass ρ hf.continuous hs x := by
  let μ : Measure ℝ := volume.restrict (Icc A B)
  let v : ℝ → TimeHilbert := fun r => deriv ρ (x-r) • vector r
  let major : ℝ → ℝ := (Icc (min 0 A) (max 0 B)).indicator (fun _ => C)
  have hv : Integrable v μ :=
    (convolutionKernel_integrable (hf.continuous_deriv le_rfl) hs.deriv x).integrableOn
  have hm : MemLp major 2 volume :=
    memLp_indicator_const 2 measurableSet_Icc C (Or.inr (by simp [Real.volume_Icc]))
  have hrep : ∀ᵐ r ∂μ, v r =ᵐ[volume] fun w => column ρ x (r,w) :=
    Eventually.of_forall fun r => by
      filter_upwards [Lp.coeFn_smul (deriv ρ (x-r)) (vector r), vector_coeFn r] with w hs hv
      rw [hs, Pi.smul_apply, hv]
      rfl
  have hparam : ∀ᵐ p : ℝ × ℝ ∂μ.prod volume, p.1 ∈ Icc A B :=
    (quasiMeasurePreserving_fst (μ := μ) (ν := volume)).ae (ae_restrict_mem measurableSet_Icc)
  have hb : ∀ᵐ p : ℝ × ℝ ∂μ.prod volume, ‖column ρ x p‖ ≤ major p.2 := by
    filter_upwards [hparam] with p hp
    have he := mul_le_mul (hbound p.1) (step_bound A B p.1 p.2 hp)
      (norm_nonneg (step p.1 p.2)) hC
    rw [column, norm_mul]
    apply he.trans_eq
    by_cases hw : p.2 ∈ Icc (min 0 A) (max 0 B) <;> simp [major,hw]
  have hcol : translatedClass ρ hf.continuous hs x =ᵐ[volume]
      fun w => ∫ r, column ρ x (r,w) ∂μ := by
    filter_upwards [translatedClass_coeFn ρ hf.continuous hs x] with w hw
    rw [hw]
    have he : (∫ r, column ρ x (r,w) ∂μ) = ∫ r, column ρ x (r,w) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by simp [column, hsupp r hr]
    rw [he, column_integral hf hs x w]
  have he := BochnerL2Fubini.integral_eq_of_slices v hv (column ρ x)
    (column_measurable hf x).aestronglyMeasurable hrep major hm hb
    (translatedClass ρ hf.continuous hs x) hcol
  have hi : (∫ r, v r ∂μ) = convolutionKernel (deriv ρ) x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun r hr => by simp [v, hsupp r hr]
  rwa [hi] at he

/-- No support radius or uniform bound is supplied by the caller. -/
theorem derivative_eq_translated {ρ : ℝ → ℝ} (hf : ContDiff ℝ 1 ρ)
    (hs : HasCompactSupport ρ) (x : ℝ) :
    convolutionKernel (deriv ρ) x = translatedClass ρ hf.continuous hs x := by
  let φ : ℝ → ℝ := fun r => deriv ρ (x-r)
  have hc : Continuous φ := (hf.continuous_deriv le_rfl).comp (continuous_const.sub continuous_id)
  have hφ : HasCompactSupport φ := hs.deriv.comp_homeomorph (Homeomorph.subLeft x)
  have hcompact : IsCompact (tsupport φ) := hφ
  obtain ⟨A,hA⟩ := hcompact.bddBelow
  obtain ⟨B,hB⟩ := hcompact.bddAbove
  obtain ⟨C,hC⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hφ.norm
  have hC0 : 0 ≤ C := (norm_nonneg (φ 0)).trans (hC ⟨0,rfl⟩)
  apply derivative_eq_translated_of_bounds hf hs x A B C hC0
  · intro r
    exact hC ⟨r,rfl⟩
  · intro r hr
    exact image_eq_zero_of_notMem_tsupport (f := φ) (fun hm => hr ⟨hA hm,hB hm⟩)

end OperatorDerivativeRewrite.Foundation.IBMPhysicalDerivativeKernel
