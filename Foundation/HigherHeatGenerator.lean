import Foundation.HigherHeatRefinement
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Actual L2 right time difference quotients on the weighted Fourier domain. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatGenerator
open HigherHeatL2

def coefficient (a t : ℝ) : ℝ := (Real.exp (-(t.toNNReal : ℝ)*a)-1)/t

theorem coefficient_bound (a : ℝ) (ha : 0 ≤ a) (t : ℝ) : |coefficient a t| ≤ a := by
  by_cases ht : 0 < t
  · have he : Real.exp (-t*a) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [coefficient,Real.coe_toNNReal t ht.le,abs_div,abs_of_pos ht,
      abs_of_nonpos (sub_nonpos.mpr he)]
    apply (div_le_iff₀ ht).mpr
    linarith [Real.add_one_le_exp (-t*a)]
  · simp [coefficient,Real.toNNReal_of_nonpos (le_of_not_gt ht),ha]

theorem coefficient_tendsto (a : ℝ) :
    Tendsto (coefficient a) (𝓝[Set.Ioi 0] 0) (𝓝 (-a)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-t*a)) (-a) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).neg.mul_const a).exp)
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (s := Set.Ioi 0) (by simp)).mp
    hd.hasDerivWithinAt
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp [coefficient,slope_def_field,Real.coe_toNNReal t ht.le]

theorem dominated_toLp_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (F : ι → ℝ → ℂ) (hF : ∀ t, MemLp (F t) 2 volume)
    (g : ℝ → ℂ) (hg : MemLp g 2 volume) (b : ℝ → ℝ) (hb : MemLp b 2 volume)
    (hbound : ∀ᶠ t in l, ∀ᵐ x ∂volume, ‖F t x‖ ≤ b x)
    (hgbound : ∀ᵐ x ∂volume, ‖g x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun t => F t x) l (𝓝 (g x))) :
    Tendsto (fun t => (hF t).toLp (F t)) l (𝓝 (hg.toLp g)) := by
  have hi := tendsto_integral_filter_of_dominated_convergence
    (l := l) (μ := volume) (F := fun t x => ‖F t x-g x‖^2) (f := fun _ => (0 : ℝ))
    (fun x => 4*(b x)^2)
    (Eventually.of_forall fun t => ((hF t).aestronglyMeasurable.sub hg.aestronglyMeasurable).norm.pow 2)
    (by
      filter_upwards [hbound] with t ht
      filter_upwards [ht,hgbound] with x hx hgx
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have he : ‖F t x-g x‖ ≤ 2*b x := (norm_sub_le _ _).trans (by linarith)
      calc
        ‖F t x-g x‖^2 ≤ (2*b x)^2 := by gcongr
        _ = 4*(b x)^2 := by ring)
    (hb.integrable_sq.const_mul 4)
    (by
      filter_upwards [hlim] with x hx
      simpa using ((hx.sub (tendsto_const_nhds (x := g x))).norm.pow 2))
  have he (t : ι) : ‖(hF t).toLp (F t)-hg.toLp g‖^2 = ∫ x, ‖F t x-g x‖^2 := by
    rw [BochnerL2Dominated.norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hF t).toLp (F t)) (hg.toLp g),
      (hF t).coeFn_toLp,hg.coeFn_toLp] with x h1 h2 h3
    simp only [h1,Pi.sub_apply,h2,h3]
  simp only [integral_zero] at hi
  have hn : Tendsto (fun t => ‖(hF t).toLp (F t)-hg.toLp g‖^2) l (𝓝 0) := by simpa only [he] using hi
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero]
    using Real.continuous_sqrt.continuousAt.tendsto.comp hn

def weight (m : ℕ) (x : ℝ) : ℝ := (2*Real.pi*x)^(2*m)

theorem weight_nonneg (m : ℕ) (x : ℝ) : 0 ≤ weight m x := by
  unfold weight
  rw [pow_mul]
  positivity

def target (m : ℕ) (f : H) (x : ℝ) : ℂ := ((-weight m x : ℝ) : ℂ)*f x

def quotient (m : ℕ) (f : H) (t x : ℝ) : ℂ := (coefficient (weight m x) t : ℂ)*f x

theorem quotient_bound (m : ℕ) (f : H) (t x : ℝ) : ‖quotient m f t x‖ ≤ ‖target m f x‖ := by
  simp only [quotient,target,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_neg,
    abs_of_nonneg (weight_nonneg m x)]
  exact mul_le_mul_of_nonneg_right (coefficient_bound _ (weight_nonneg m x) t) (norm_nonneg _)

theorem quotient_memLp (m : ℕ) (f : H) (hf : MemLp (target m f) 2 volume) (t : ℝ) :
    MemLp (quotient m f t) 2 volume := by
  have hc : Continuous (fun x : ℝ => (coefficient (weight m x) t : ℂ)) := by
    unfold coefficient weight
    fun_prop
  apply hf.of_le (hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  exact Eventually.of_forall (quotient_bound m f t)

theorem quotient_tendsto (m : ℕ) (f : H) (hf : MemLp (target m f) 2 volume) :
    Tendsto (fun t : ℝ => (quotient_memLp m f hf t).toLp (quotient m f t))
      (𝓝[Set.Ioi 0] 0) (𝓝 (hf.toLp (target m f))) := by
  apply dominated_toLp_filter (quotient m f) (quotient_memLp m f hf)
    (target m f) hf (fun x => ‖target m f x‖) hf.norm
    (Eventually.of_forall fun t => Eventually.of_forall (quotient_bound m f t))
    (Eventually.of_forall fun _ => le_rfl)
  exact Eventually.of_forall fun x => by
    have h := (Complex.continuous_ofReal.tendsto (-weight m x)).comp
      (coefficient_tendsto (weight m x))
    exact h.mul_const (f x)

theorem quotient_identification (m : ℕ) (f : H) (hf : MemLp (target m f) 2 volume) (t : ℝ) :
    (quotient_memLp m f hf t).toLp (quotient m f t) =
      t⁻¹ • (multiplier m t.toNNReal f-f) := by
  apply Lp.ext
  filter_upwards [(quotient_memLp m f hf t).coeFn_toLp,
    Lp.coeFn_smul (t⁻¹ : ℝ) (multiplier m t.toNNReal f-f),
    Lp.coeFn_sub (multiplier m t.toNNReal f) f,multiplier_ae m t.toNNReal f] with x h1 h2 h3 h4
  simp only [h1,h2,Pi.smul_apply,h3,Pi.sub_apply,h4,quotient,coefficient,weight,symbol,
    Complex.real_smul]
  push_cast
  ring

theorem multiplier_difference_quotient (m : ℕ) (f : H) (hf : MemLp (target m f) 2 volume) :
    Tendsto (fun t : ℝ => t⁻¹ • (multiplier m t.toNNReal f-f))
      (𝓝[Set.Ioi 0] 0) (𝓝 (hf.toLp (target m f))) := by
  have he : (fun t : ℝ => (quotient_memLp m f hf t).toLp (quotient m f t)) =
      (fun t : ℝ => t⁻¹ • (multiplier m t.toNNReal f-f)) := by
    funext t
    exact quotient_identification m f hf t
  rw [← he]
  exact quotient_tendsto m f hf

def generator (m : ℕ) (f : H) (hf : MemLp (target m (𝓕 f)) 2 volume) : H :=
  𝓕⁻ (hf.toLp (target m (𝓕 f)))

theorem evolution_difference_quotient (m : ℕ) (f : H)
    (hf : MemLp (target m (𝓕 f)) 2 volume) :
    Tendsto (fun t : ℝ => t⁻¹ • (evolution m t.toNNReal f-f))
      (𝓝[Set.Ioi 0] 0) (𝓝 (generator m f hf)) := by
  have h := ((fourierInvCLM ℂ H).continuous.tendsto (hf.toLp (target m (𝓕 f)))).comp
    (multiplier_difference_quotient m (𝓕 f) hf)
  have he : (fun t : ℝ => (fourierInvCLM ℂ H) (t⁻¹ • (multiplier m t.toNNReal (𝓕 f)-𝓕 f))) =
      (fun t : ℝ => t⁻¹ • (evolution m t.toNNReal f-f)) := by
    funext t
    rw [ContinuousLinearMap.map_smul_of_tower,map_sub]
    change t⁻¹ • (𝓕⁻ (multiplier m t.toNNReal (𝓕 f))-𝓕⁻ (𝓕 f)) = _
    rw [fourierInv_fourier_eq,evolution_apply]
  change Tendsto (fun t : ℝ => (fourierInvCLM ℂ H)
    (t⁻¹ • (multiplier m t.toNNReal (𝓕 f)-𝓕 f))) _ _ at h
  rw [he] at h
  exact h

theorem evolution_hasDerivWithinAt (m : ℕ) (f : H)
    (hf : MemLp (target m (𝓕 f)) 2 volume) :
    HasDerivWithinAt (fun t : ℝ => evolution m t.toNNReal f)
      (generator m f hf) (Set.Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext t
    change (0 ≤ t ∧ t ≠ 0) ↔ 0 < t
    constructor
    · rintro ⟨h1,h2⟩
      exact lt_of_le_of_ne h1 (Ne.symm h2)
    · intro h
      exact ⟨h.le,ne_of_gt h⟩

  rw [hset]
  have he : slope (fun t : ℝ => evolution m t.toNNReal f) 0 =
      (fun t : ℝ => t⁻¹ • (evolution m t.toNNReal f-f)) := by
    funext t
    simp only [slope_def_module,sub_zero,Real.toNNReal_zero,evolution_zero,ContinuousLinearMap.id_apply]
  rw [he]
  exact evolution_difference_quotient m f hf

end OperatorDerivativeRewrite.Foundation.HigherHeatGenerator
