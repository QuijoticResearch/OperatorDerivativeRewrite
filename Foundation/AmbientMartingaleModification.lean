import Foundation.AmbientNullAugmentation
import Mathlib.Probability.Martingale.Basic

/-! Ambient-measurable coordinate modifications become genuine martingales
after explicit ambient null augmentation of the original filtration. -/
noncomputable section
open MeasureTheory Filter
namespace OperatorDerivativeRewrite.Foundation.AmbientMartingaleModification
open AmbientNullAugmentation
set_option backward.isDefEq.respectTransparency false
variable {Ω ι : Type*} [m : MeasurableSpace Ω] [Preorder ι]
  (μ : Measure Ω) [IsFiniteMeasure μ] (ℱ : Filtration ι m)

theorem martingale_modification (M N : ι → Ω → ℝ) (hM : Martingale M ℱ μ)
    (hN : ∀ t, Measurable (N t)) (he : ∀ t, N t =ᵐ[μ] M t) :
    Martingale N (filtration μ ℱ) μ := by
  refine ⟨?_, ?_⟩
  · intro t
    exact (measurable_of_raw_aestronglyMeasurable (ℱ t) μ (hN t)
      ((hM.stronglyAdapted t).aestronglyMeasurable.congr (he t).symm)).stronglyMeasurable
  · intro s t hst
    have hi : Integrable (N t) μ := (hM.integrable t).congr (he t).symm
    exact (condExp_invariant (ℱ s) μ (ℱ.le s) (N t) hi).symm.trans
      ((condExp_congr_ae (he t)).trans ((hM.condExp_ae_eq hst).trans (he s).symm))

theorem martingale_augmented (M : ι → Ω → ℝ) (hM : Martingale M ℱ μ) :
    Martingale M (filtration μ ℱ) μ :=
  martingale_modification μ ℱ M M hM
    (fun t => (hM.stronglyAdapted t).measurable.mono (ℱ.le t) le_rfl)
    (fun _ => Filter.EventuallyEq.rfl)

end OperatorDerivativeRewrite.Foundation.AmbientMartingaleModification
