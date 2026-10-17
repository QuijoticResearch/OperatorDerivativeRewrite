import Foundation.HigherHeatClosedGenerator
import Foundation.FixedLawPathObstruction

/-! Exact infinitesimal-generator graph of the constructed L2 heat evolution. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatGeneratorDomain
set_option backward.isDefEq.respectTransparency false
open HigherHeatL2 HigherHeatGenerator HigherHeatClosedGenerator

theorem quotient_ae (m : ℕ) (f : H) (t : ℝ) :
    ((t⁻¹ • (multiplier m t.toNNReal f-f) : H) : ℝ → ℂ) =ᵐ[volume] quotient m f t := by
  filter_upwards [Lp.coeFn_smul (t⁻¹ : ℝ) (multiplier m t.toNNReal f-f),
    Lp.coeFn_sub (multiplier m t.toNNReal f) f,multiplier_ae m t.toNNReal f] with x h1 h2 h3
  simp only [h1,Pi.smul_apply,h2,Pi.sub_apply,h3,quotient,coefficient,weight,symbol,
    Complex.real_smul]
  push_cast
  ring

theorem multiplier_limit_implies_graph (m : ℕ) (f g : H)
    (hlim : Tendsto (fun t : ℝ => t⁻¹ • (multiplier m t.toNNReal f-f))
      (𝓝[Set.Ioi 0] 0) (𝓝 g)) : target m f =ᵐ[volume] g := by
  have hs := hlim.comp FixedLawPathObstruction.smallTime_tendsto_right
  obtain ⟨ns,hns,hn⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂volume, ∀ n : ℕ,
      ((FixedLawPathObstruction.smallTime n)⁻¹ •
        (multiplier m (FixedLawPathObstruction.smallTime n).toNNReal f-f) : H) x =
          quotient m f (FixedLawPathObstruction.smallTime n) x :=
    ae_all_iff.mpr (fun n => quotient_ae m f _)
  filter_upwards [hn,hall] with x hx hall
  have hpoint := ((Complex.continuous_ofReal.tendsto (-weight m x)).comp
    (coefficient_tendsto (weight m x))).mul_const (f x)
  have ht := hpoint.comp (FixedLawPathObstruction.smallTime_tendsto_right.comp hns.tendsto_atTop)
  change Tendsto (fun k => quotient m f (FixedLawPathObstruction.smallTime (ns k)) x)
    atTop (𝓝 (target m f x)) at ht
  have he : (fun k => ((FixedLawPathObstruction.smallTime (ns k))⁻¹ •
      (multiplier m (FixedLawPathObstruction.smallTime (ns k)).toNNReal f-f) : H) x) =
      (fun k => quotient m f (FixedLawPathObstruction.smallTime (ns k)) x) := by
    funext k
    exact hall _
  change Tendsto (fun k => ((FixedLawPathObstruction.smallTime (ns k))⁻¹ •
      (multiplier m (FixedLawPathObstruction.smallTime (ns k)).toNNReal f-f) : H) x)
    atTop (𝓝 (g x)) at hx
  rw [he] at hx
  exact tendsto_nhds_unique ht hx

theorem multiplier_limit_iff (m : ℕ) (f g : H) :
    Tendsto (fun t : ℝ => t⁻¹ • (multiplier m t.toNNReal f-f))
      (𝓝[Set.Ioi 0] 0) (𝓝 g) ↔ target m f =ᵐ[volume] g := by
  constructor
  · exact multiplier_limit_implies_graph m f g
  · intro h
    have hf : MemLp (target m f) 2 volume := (memLp_congr_ae h).mpr (Lp.memLp g)
    have he : hf.toLp (target m f)=g := by
      apply Lp.ext
      exact hf.coeFn_toLp.trans h
    rw [← he]
    exact multiplier_difference_quotient m f hf

theorem evolution_limit_iff (m : ℕ) (f g : H) :
    Tendsto (fun t : ℝ => t⁻¹ • (evolution m t.toNNReal f-f))
      (𝓝[Set.Ioi 0] 0) (𝓝 g) ↔ (f,g) ∈ (operator m).graph := by
  constructor
  · intro hlim
    have h := ((fourierCLM ℂ H).continuous.tendsto g).comp hlim
    have he : (fun t : ℝ => (fourierCLM ℂ H) (t⁻¹ • (evolution m t.toNNReal f-f))) =
        (fun t : ℝ => t⁻¹ • (multiplier m t.toNNReal (𝓕 f)-𝓕 f)) := by
      funext t
      rw [ContinuousLinearMap.map_smul_of_tower,map_sub]
      change t⁻¹ • (𝓕 (evolution m t.toNNReal f)-𝓕 f) = _
      rw [evolution_apply,fourier_fourierInv_eq]
    change Tendsto (fun t : ℝ => (fourierCLM ℂ H) (t⁻¹ • (evolution m t.toNNReal f-f))) _ _ at h
    rw [he] at h
    rw [operator_graph,graph_iff]
    exact (multiplier_limit_iff m (𝓕 f) (𝓕 g)).mp h
  · intro hg
    have hmem : f ∈ (operator m).domain := LinearPMap.mem_domain_iff.mpr ⟨g,hg⟩
    have hf := (domain_iff m f).mp hmem
    have he : generator m f hf=g :=
      (operator m).mem_graph_snd_inj (generator_mem_graph m f hf) hg rfl
    rw [← he]
    exact evolution_difference_quotient m f hf

theorem evolution_hasDerivWithinAt_iff (m : ℕ) (f g : H) :
    HasDerivWithinAt (fun t : ℝ => evolution m t.toNNReal f) g (Set.Ici 0) 0 ↔
      (f,g) ∈ (operator m).graph := by
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
  exact evolution_limit_iff m f g

theorem domain_iff_derivative (m : ℕ) (f : H) :
    f ∈ (operator m).domain ↔ ∃ g : H,
      HasDerivWithinAt (fun t : ℝ => evolution m t.toNNReal f) g (Set.Ici 0) 0 := by
  rw [LinearPMap.mem_domain_iff]
  simp only [evolution_hasDerivWithinAt_iff]

theorem weighted_iff_derivative (m : ℕ) (f : H) :
    MemLp (target m (𝓕 f)) 2 volume ↔ ∃ g : H,
      HasDerivWithinAt (fun t : ℝ => evolution m t.toNNReal f) g (Set.Ici 0) 0 := by
  rw [← domain_iff,domain_iff_derivative]

end OperatorDerivativeRewrite.Foundation.HigherHeatGeneratorDomain
