import Foundation.InfiniteGaussianIsonormal

/-! Actual measure-preserving reflection of the countable Gaussian sample,
and oddness of every first-chaos class under this same sample map. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianSampleReflection
open InfiniteGaussian
set_option backward.isDefEq.respectTransparency false

def reflect (ω : SampleSpace) : SampleSpace := fun n => -ω n

theorem reflect_preserving : MeasurePreserving reflect gaussianProduct gaussianProduct := by
  refine ⟨by unfold reflect; fun_prop, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ => GaussianCore.γ)).map
    (fun ω n => -ω n) = Measure.infinitePi (fun _ : ℕ => GaussianCore.γ)
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => GaussianCore.γ) (fun _ => measurable_neg)]
  congr 1
  funext n
  simpa only [GaussianCore.γ, neg_zero] using gaussianReal_map_neg (μ := 0) (v := 1)

def reflection : GaussianL2 →ₗᵢ[ℝ] GaussianL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ reflect reflect_preserving

theorem reflection_ae (f : GaussianL2) :
    reflection f =ᵐ[gaussianProduct] fun ω => f (reflect ω) :=
  Lp.coeFn_compMeasurePreserving f reflect_preserving

theorem reflection_coordinate (n : ℕ) : reflection (coordinateL2 n) = -coordinateL2 n := by
  apply Lp.ext
  filter_upwards [reflection_ae (coordinateL2 n),
    reflect_preserving.quasiMeasurePreserving.ae_eq_comp (coordinateL2_coeFn n),
    coordinateL2_coeFn n, Lp.coeFn_neg (coordinateL2 n)] with ω hr hc ho hn
  simp only [Function.comp_def] at hc
  rw [hr, hc, hn, Pi.neg_apply, ho]
  rfl

theorem reflection_firstChaos (h : CoefficientSpace) :
    reflection (firstChaosEmbedding h) = -firstChaosEmbedding h := by
  have hs := (firstChaos_hasSum h).map reflection.toLinearMap.toAddMonoidHom reflection.continuous
  change HasSum (fun n => reflection (h n • coordinateL2 n))
    (reflection (firstChaosEmbedding h)) at hs
  simp only [map_smul, reflection_coordinate] at hs
  have ht : HasSum (fun n => h n • (-coordinateL2 n)) (-firstChaosEmbedding h) := by
    simpa only [smul_neg] using (firstChaos_hasSum h).neg
  exact hs.unique ht

theorem firstChaos_reflect_ae (h : CoefficientSpace) :
    (fun ω => firstChaosEmbedding h (reflect ω)) =ᵐ[gaussianProduct]
      fun ω => -firstChaosEmbedding h ω := by
  have hr := reflection_ae (firstChaosEmbedding h)
  rw [reflection_firstChaos] at hr
  exact hr.symm.trans (Lp.coeFn_neg (firstChaosEmbedding h))

end OperatorDerivativeRewrite.Foundation.GaussianSampleReflection
