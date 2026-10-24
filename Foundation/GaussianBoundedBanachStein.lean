import Foundation.GaussianBoundedHeatDerivative

/-! Gaussian Stein identities for complete real Banach values with an actual
everywhere derivative and bounded measurable derivative field. The proof
reuses the verified likelihood derivative, not a stronger C2 hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianBoundedBanachStein
open GaussianCore GaussianBoundedTiltDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem stein (F D : ℝ → E) (hd : ∀ x, HasDerivAt F (D x) x)
    (hD : StronglyMeasurable D) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hFbound : ∀ x, ‖F x‖ ≤ M) (hDbound : ∀ x, ‖D x‖ ≤ B) :
    (∫ z : ℝ, z • F z ∂γ) = ∫ z : ℝ, D z ∂γ := by
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  let A : ℝ → ℝ → E := fun t z => F (z+t)
  let G : ℝ → ℝ → E := fun t z => D (z+t)
  have hmeas (t : ℝ) : AEStronglyMeasurable (A t) γ :=
    (hc.comp (continuous_id.add_const t)).aestronglyMeasurable
  have hint : Integrable (A 0) γ := (integrable_const M).mono' (hmeas 0)
    (Filter.Eventually.of_forall fun z => hFbound _)
  have hgmeas : AEStronglyMeasurable (G 0) γ :=
    (hD.comp_measurable (measurable_id.add_const 0)).aestronglyMeasurable
  have hbound : ∀ᵐ z ∂γ, ∀ t ∈ (univ : Set ℝ), ‖G t z‖ ≤ B :=
    Filter.Eventually.of_forall fun z t _ => hDbound _
  have hdiff : ∀ᵐ z ∂γ, ∀ t ∈ (univ : Set ℝ),
      HasDerivAt (fun s => A s z) (G t z) t := by
    filter_upwards with z t _
    simpa only [Function.comp_def,one_smul] using
      (hd (z+t)).scomp t ((hasDerivAt_id t).const_add z)
  obtain ⟨_,hi⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := A) (F' := G) (μ := γ) (s := univ) (x₀ := (0 : ℝ))
    Filter.univ_mem (Filter.Eventually.of_forall hmeas) hint hgmeas hbound (integrable_const B) hdiff
  have hi' : HasDerivAt (fun t => ∫ z : ℝ, F (z+t) ∂γ) (∫ z : ℝ, D z ∂γ) 0 := by
    simpa only [A,G,add_zero] using hi
  exact (translate_hasDerivAt_zero F hc M hM hFbound).unique hi'

theorem scaled_stein (F D : ℝ → E) (hd : ∀ x, HasDerivAt F (D x) x)
    (hD : StronglyMeasurable D) (M B : ℝ) (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hFbound : ∀ x, ‖F x‖ ≤ M) (hDbound : ∀ x, ‖D x‖ ≤ B) (b : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x • F (b+x) ∂gaussianReal 0 v) =
      (v : ℝ) • ∫ x : ℝ, D (b+x) ∂gaussianReal 0 v := by
  let σ : ℝ := Real.sqrt v
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  have hc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hder (z : ℝ) : HasDerivAt (fun t : ℝ => F (b+σ*t)) (σ • D (b+σ*z)) z := by
    simpa only [Function.comp_def,id_eq,mul_one] using
      (hd (b+σ*z)).scomp z (((hasDerivAt_id z).const_mul σ).const_add b)
  have hmeas : StronglyMeasurable (fun z : ℝ => σ • D (b+σ*z)) :=
    (hD.comp_measurable (measurable_const.add (measurable_const.mul measurable_id))).const_smul σ
  have hbnd (z : ℝ) : ‖σ • D (b+σ*z)‖ ≤ σ*B := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_left (hDbound _) hσ
  have hs := stein (fun z : ℝ => F (b+σ*z)) (fun z : ℝ => σ • D (b+σ*z))
    hder hmeas M (σ*B) hM (mul_nonneg hσ hB) (fun z => hFbound _) hbnd
  have hl : HasLaw (fun z : ℝ => σ*z) (gaussianReal 0 v) γ := by
    refine ⟨by fun_prop,?_⟩
    simp [γ,σ,gaussianReal_map_const_mul,Real.sq_sqrt v.coe_nonneg]
  have hf : AEStronglyMeasurable (fun x : ℝ => x • F (b+x)) (gaussianReal 0 v) :=
    (continuous_id.smul (hc.comp (continuous_const.add continuous_id))).aestronglyMeasurable
  have hg : AEStronglyMeasurable (fun x : ℝ => D (b+x)) (gaussianReal 0 v) :=
    (hD.comp_measurable (measurable_const.add measurable_id)).aestronglyMeasurable
  calc
    _ = ∫ z : ℝ, (σ*z) • F (b+σ*z) ∂γ := (hl.integral_comp hf).symm
    _ = σ • ∫ z : ℝ, z • F (b+σ*z) ∂γ := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (σ*z) • F (b+σ*z) = σ • z • F (b+σ*z)
        rw [smul_smul]
    _ = σ • ∫ z : ℝ, σ • D (b+σ*z) ∂γ := congrArg (fun w : E => σ • w) hs
    _ = (v : ℝ) • ∫ z : ℝ, D (b+σ*z) ∂γ := by
      rw [integral_smul,smul_smul]
      have he : σ*σ = (v : ℝ) := by simpa only [pow_two] using Real.sq_sqrt v.coe_nonneg
      rw [he]
    _ = _ := congrArg (fun w : E => (v : ℝ) • w) (hl.integral_comp hg)

end OperatorDerivativeRewrite.Foundation.GaussianBoundedBanachStein
