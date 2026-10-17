import Foundation.HigherHeatCylindricalOperator

/-! Actual all-time Schwartz evolution and its semigroup law through the verified L2 realization. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzSemigroup
open HigherHeatL2 HigherHeatSignedLaws GaussianSchwartzKernel

def evolve (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  if ht : 0 < t then
    SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (evenKernel m hm t ht) f
  else f

theorem evolve_zero (m : ℕ) (hm : 0 < m) (f : 𝓢(ℝ,ℂ)) : evolve m hm 0 f=f := by
  simp [evolve]

theorem evolve_positive (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (f : 𝓢(ℝ,ℂ)) :
    evolve m hm t f=SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (evenKernel m hm t ht) f := by
  simp only [evolve,dif_pos ht]

theorem evolve_toLp (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    (evolve m hm t f).toLp 2 volume=HigherHeatL2.evolution m t (f.toLp 2 volume) := by
  by_cases ht : 0 < t
  · rw [evolve_positive m hm t ht]
    exact (l2_kernel_evolution m hm t ht f).symm
  · have ht0 : t=0 := le_antisymm (le_of_not_gt ht) (by positivity)
    subst t
    rw [evolve_zero,HigherHeatL2.evolution_zero,ContinuousLinearMap.id_apply]

theorem toLp_injective : Function.Injective (fun f : 𝓢(ℝ,ℂ) => f.toLp 2 volume) := by
  intro f g h
  change f.toLp 2 volume=g.toLp 2 volume at h
  apply DFunLike.coe_injective
  apply (f.continuous.ae_eq_iff_eq volume g.continuous).mp
  filter_upwards [f.coeFn_toLp 2 volume,g.coeFn_toLp 2 volume] with x hx hy
  rw [← hx,← hy,h]

theorem evolve_add (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    evolve m hm s (evolve m hm t f)=evolve m hm (s+t) f := by
  apply toLp_injective
  simp only [evolve_toLp]
  exact congrArg (fun A : H →L[ℂ] H => A (f.toLp 2 volume)) (evolution_semigroup m s t)

theorem evolve_linear_add (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (f g : 𝓢(ℝ,ℂ)) :
    evolve m hm t (f+g)=evolve m hm t f+evolve m hm t g := by
  apply toLp_injective
  change (evolve m hm t (f+g)).toLp 2 volume=
    (evolve m hm t f).toLp 2 volume+(evolve m hm t g).toLp 2 volume
  simp only [evolve_toLp]
  change HigherHeatL2.evolution m t (f.toLp 2 volume+g.toLp 2 volume)=_
  exact map_add _ _ _

theorem evolve_linear_smul (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (c : ℂ) (f : 𝓢(ℝ,ℂ)) :
    evolve m hm t (c • f)=c • evolve m hm t f := by
  apply toLp_injective
  change (evolve m hm t (c • f)).toLp 2 volume=c • (evolve m hm t f).toLp 2 volume
  simp only [evolve_toLp]
  change HigherHeatL2.evolution m t (c • f.toLp 2 volume)=_
  exact map_smul _ _ _

theorem evolve_l2_bound (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (f : 𝓢(ℝ,ℂ)) :
    ‖(evolve m hm t f).toLp 2 volume‖ ≤ ‖f.toLp 2 volume‖ := by
  rw [evolve_toLp]
  exact evolution_contraction m t _

end OperatorDerivativeRewrite.Foundation.HigherHeatSchwartzSemigroup
