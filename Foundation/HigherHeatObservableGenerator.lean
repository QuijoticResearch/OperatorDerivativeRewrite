import Foundation.HigherHeatBackwardSchwartz
import Foundation.HigherHeatSchwartzJets
import Mathlib.Analysis.InnerProductSpace.Dual

/-! The actual higher-heat observable generator via continuous L2 test pairing. -/
noncomputable section
open MeasureTheory FourierTransform
open scoped SchwartzMap NNReal Topology
namespace OperatorDerivativeRewrite.Foundation.HigherHeatObservableGenerator
open HigherHeatL2 HigherHeatSpatialGenerator HigherHeatSchwartzJets GaussianSchwartzKernel
open HigherHeatSchwartzSemigroup HigherHeatBackwardSchwartz

def conjugateTest (f : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  f.postcompCLM Complex.conjCLE.toContinuousLinearMap

def testPairing (f : 𝓢(ℝ,ℂ)) : H →L[ℂ] ℂ := innerSL ℂ ((conjugateTest f).toLp 2 volume)

theorem testPairing_schwartz (f g : 𝓢(ℝ,ℂ)) :
    testPairing f (g.toLp 2 volume)=∫ x : ℝ, f x*g x := by
  change inner ℂ ((conjugateTest f).toLp 2 volume) (g.toLp 2 volume)=_
  rw [SchwartzMap.inner_toL2_toL2_eq (conjugateTest f) g volume]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change inner ℂ (starRingEnd ℂ (f x)) (g x)=f x*g x
    simp only [RCLike.inner_apply,starRingEnd_apply,star_star]
    ring

theorem differential_pairing (m : ℕ) (f g : 𝓢(ℝ,ℂ)) :
    (∫ x : ℝ, f x*differential m g x)=(∫ x : ℝ, differential m f x*g x) := by
  have h := integral_jet_mul (2*m) f g
  have hp : (-1:ℂ)^(2*m)=1 := by rw [pow_mul]; norm_num
  rw [hp,one_mul] at h
  calc
    _ = (-1:ℂ)^(m+1)*(∫ x : ℝ, f x*jet (2*m) g x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [differential,SchwartzMap.smul_apply,smul_eq_mul]
        ring
    _ = (-1:ℂ)^(m+1)*(∫ x : ℝ, jet (2*m) f x*g x) := by rw [h]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [differential,SchwartzMap.smul_apply,smul_eq_mul]
        ring

theorem evolve_kernel (m : ℕ) (hm : 0 < m) (s T : ℝ≥0) (hT : 0 < T) :
    evolve m hm s (evenKernel m hm T hT)=evenKernel m hm (s+T) (by positivity) := by
  apply (fourierEquiv ℂ 𝓢(ℝ,ℂ)).injective
  ext ξ
  change 𝓕 (evolve m hm s (evenKernel m hm T hT)) ξ=𝓕 (evenKernel m hm (s+T) _) ξ
  rw [evolve_fourier,evenKernel_fourier,evenKernel_fourier,evenSymbol_apply,evenSymbol_apply,symbol_add]

theorem pairing_kernel_mean (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℂ)) :
    testPairing f ((evenKernel m hm T hT).toLp 2 volume)=HigherHeatSchwartzCalculus.mean m T f := by
  rw [testPairing_schwartz]
  simpa only [HigherHeatSignedLaws.realKernel_coe] using
    (HigherHeatSchwartzCalculus.mean_eq_kernel m hm T hT f).symm

theorem pairing_evolution_kernel (m : ℕ) (hm : 0 < m) (s T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℂ)) :
    testPairing f (HigherHeatL2.evolution m s ((evenKernel m hm T hT).toLp 2 volume))=
      HigherHeatSchwartzCalculus.mean m (s+T) f := by
  rw [← evolve_toLp m hm s (evenKernel m hm T hT),evolve_kernel m hm s T hT,pairing_kernel_mean]

theorem pairing_generator_kernel (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (f : 𝓢(ℝ,ℂ)) :
    testPairing f ((differential m (evenKernel m hm T hT)).toLp 2 volume)=
      HigherHeatSchwartzCalculus.mean m T (differential m f) := by
  rw [testPairing_schwartz,differential_pairing]
  simpa only [HigherHeatSignedLaws.realKernel_coe] using
    (HigherHeatSchwartzCalculus.mean_eq_kernel m hm T hT (differential m f)).symm

theorem shifted_observable_hasDerivWithinAt (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (f : 𝓢(ℝ,ℂ)) :
    HasDerivWithinAt (fun h : ℝ => HigherHeatSchwartzCalculus.mean m (T+h.toNNReal) f)
      (HigherHeatSchwartzCalculus.mean m T (differential m f)) (Set.Ici 0) 0 := by
  have hd := HigherHeatSpatialGenerator.evolution_hasDerivWithinAt m (evenKernel m hm T hT)
  have hD := ((testPairing f).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt 0 hd
  change HasDerivWithinAt
    (fun h : ℝ => testPairing f (HigherHeatL2.evolution m h.toNNReal ((evenKernel m hm T hT).toLp 2 volume)))
    (testPairing f ((differential m (evenKernel m hm T hT)).toLp 2 volume)) (Set.Ici 0) 0 at hD
  have he : (fun h : ℝ => testPairing f
      (HigherHeatL2.evolution m h.toNNReal ((evenKernel m hm T hT).toLp 2 volume)))=
      (fun h : ℝ => HigherHeatSchwartzCalculus.mean m (T+h.toNNReal) f) := by
    funext h
    simpa only [add_comm] using pairing_evolution_kernel m hm h.toNNReal T hT f
  rw [he,pairing_generator_kernel m hm T hT f] at hD
  exact hD

end OperatorDerivativeRewrite.Foundation.HigherHeatObservableGenerator
