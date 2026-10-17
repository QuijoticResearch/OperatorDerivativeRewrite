import Foundation.HigherHeatMarginals
import Mathlib.MeasureTheory.Group.Prod

/-! Adding two genuine signed heat increments gives the heat law at summed time. -/
noncomputable section
open MeasureTheory
open scoped NNReal SchwartzMap Topology Convolution
namespace OperatorDerivativeRewrite.Foundation.HigherHeatRefinement
open GaussianSchwartzKernel HigherHeatSignedLaws

def subtractSecond : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun z := (z.1-z.2,z.2)
  invFun z := (z.1+z.2,z.2)
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  measurable_toFun := by
    change Measurable (fun z : ℝ × ℝ => (z.1-z.2,z.2))
    exact (measurable_fst.sub measurable_snd).prodMk measurable_snd
  measurable_invFun := by
    change Measurable (fun z : ℝ × ℝ => (z.1+z.2,z.2))
    exact (measurable_fst.add measurable_snd).prodMk measurable_snd

theorem realKernel_convolution (m : ℕ) (hm : 0 < m) (s t : ℝ≥0)
    (hs : 0 < s) (ht : 0 < t) (x : ℝ) :
    (∫ y : ℝ, realKernel m hm s hs y * realKernel m hm t ht (x-y)) =
      realKernel m hm (s+t) (add_pos hs ht) x := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [Complex.ofReal_mul,realKernel_coe]
  have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f x) (evenKernel_convolution m hm s t hs ht)
  rw [SchwartzMap.convolution_apply,convolution_def] at h
  exact h

def pairLaw (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    SignedMeasure (ℝ × ℝ) := (volume.prod volume).withDensityᵥ
      (fun z => realKernel m hm s hs z.1 * realKernel m hm t ht z.2)

theorem pairLaw_integrable (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    Integrable (fun z : ℝ × ℝ => realKernel m hm s hs z.1 * realKernel m hm t ht z.2)
      (volume.prod volume) :=
  (realKernel m hm s hs).integrable.mul_prod (realKernel m hm t ht).integrable

theorem add_pairLaw (m : ℕ) (hm : 0 < m) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t) :
    (pairLaw m hm s t hs ht).map (fun z : ℝ × ℝ => z.1+z.2) =
      law m hm (s+t) (add_pos hs ht) := by
  have he : MeasurePreserving subtractSecond (volume.prod volume) (volume.prod volume) :=
    measurePreserving_sub_prod volume volume
  have hi := pairLaw_integrable m hm s t hs ht
  have hc : Integrable (fun z : ℝ × ℝ =>
      realKernel m hm s hs (z.1-z.2) * realKernel m hm t ht z.2) (volume.prod volume) := by
    exact (he.integrable_comp_emb subtractSecond.measurableEmbedding).mpr hi
  have hadd : Measurable (fun z : ℝ × ℝ => z.1+z.2) := by fun_prop
  ext A hA
  rw [VectorMeasure.map_apply _ hadd hA,pairLaw,
    withDensityᵥ_apply hi (hadd hA),law_apply _ _ _ _ _ hA]
  rw [← he.setIntegral_preimage_emb subtractSecond.measurableEmbedding
    (fun z : ℝ × ℝ => realKernel m hm s hs z.1 * realKernel m hm t ht z.2)
    ((fun z : ℝ × ℝ => z.1+z.2) ⁻¹' A)]
  have hset : subtractSecond ⁻¹' ((fun z : ℝ × ℝ => z.1+z.2) ⁻¹' A) =
      A ×ˢ Set.univ := by ext z; simp [subtractSecond]
  rw [hset]
  change (∫ z in A ×ˢ Set.univ, realKernel m hm s hs (z.1-z.2) *
    realKernel m hm t ht z.2 ∂(volume.prod volume)) = _
  rw [setIntegral_prod _ hc.integrableOn,Measure.restrict_univ]
  apply setIntegral_congr_fun hA
  intro x hx
  change (∫ y : ℝ, realKernel m hm s hs (x-y) * realKernel m hm t ht y) = _
  simpa only [mul_comm,add_comm] using realKernel_convolution m hm t s ht hs x

end OperatorDerivativeRewrite.Foundation.HigherHeatRefinement
