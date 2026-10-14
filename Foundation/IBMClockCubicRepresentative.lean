import Foundation.BochnerL2RepresentativeFubini
import Foundation.IBMClockCubicSourcePrimitive

/-! Actual scalar cubic time integrals represent the recovered scenery L2 class,
for every constructed clock path. Joint clock moments remain separate. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.IBMClockCubicRepresentative
open InfiniteGaussian IBMClockCubicCorrection IBMClockCubicSourcePrimitive
open IBMClockCubicTimeProjection BochnerL2RepresentativeFubini
attribute [local irreducible] IBMConstructedSources.mollifiedValue IBMDyadicExtension.field

def timeRepresentative (n : ℕ) (ωY : SampleSpace) (p : ℝ × SampleSpace) : ℝ :=
  value n (Real.toNNReal p.1) (p.2,ωY)

theorem timeRepresentative_measurable (n : ℕ) (ωY : SampleSpace) :
    Measurable (timeRepresentative n ωY) := by
  have hm : Measurable (fun p : ℝ × SampleSpace => (Real.toNNReal p.1,(p.2,ωY))) :=
    (measurable_real_toNNReal.comp measurable_fst).prodMk
      (measurable_snd.prodMk measurable_const)
  exact (value_jointly_measurable n).comp hm

def integratedValue (n : ℕ) (ωY : SampleSpace) (T : ℝ) (ωX : SampleSpace) : ℝ :=
  ∫ s in Set.Icc 0 T, value n (Real.toNNReal s) (ωX,ωY)

theorem timeRepresentative_integrable (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    Integrable (timeRepresentative n ωY)
      ((volume.restrict (Set.Icc 0 T)).prod gaussianProduct) := by
  exact representative_integrable (fun s : ℝ => sectionClass n (Real.toNNReal s) ωY)
    (sectionClass_time_integrable n ωY T) (timeRepresentative n ωY)
    (timeRepresentative_measurable n ωY).aestronglyMeasurable
    (Eventually.of_forall fun s => sectionClass_coeFn n (Real.toNNReal s) ωY)

theorem integratedCorrection_coeFn (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    integratedCorrection n ωY T =ᵐ[gaussianProduct] integratedValue n ωY T :=
  integral_coeFn_ae (fun s : ℝ => sectionClass n (Real.toNNReal s) ωY)
    (sectionClass_time_integrable n ωY T) (timeRepresentative n ωY)
    (timeRepresentative_measurable n ωY).aestronglyMeasurable
    (Eventually.of_forall fun s => sectionClass_coeFn n (Real.toNNReal s) ωY)

theorem integratedValue_memLp (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    MemLp (integratedValue n ωY T) 2 gaussianProduct :=
  (Lp.memLp (integratedCorrection n ωY T)).ae_eq (integratedCorrection_coeFn n ωY T)

theorem integratedValue_centered (n : ℕ) (ωY : SampleSpace) (T : ℝ) :
    (∫ ωX, integratedValue n ωY T ωX ∂gaussianProduct)=0 := by
  rw [← integral_congr_ae (integratedCorrection_coeFn n ωY T),
    ← gaussianOne_inner_eq_integral,integratedCorrection_centered]

end OperatorDerivativeRewrite.Foundation.IBMClockCubicRepresentative
