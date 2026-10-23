import Foundation.BochnerL2Fubini

/-! Construct the column L2 class required by the existing Bochner Fubini
theorem, from its genuine L2 majorant. The second measure may be infinite. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.BochnerL2MajorantRealization
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [SFinite ν]

omit [CompleteSpace E] in
theorem column_memLp (g : X × Y → E) (hg : StronglyMeasurable g)
    (B : Y → ℝ) (hB : MemLp B 2 ν)
    (hb : ∀ᵐ p ∂μ.prod ν, ‖g p‖ ≤ B p.2) :
    MemLp (fun y => ∫ x, g (x, y) ∂μ) 2 ν := by
  apply (hB.const_mul (μ.real Set.univ)).mono'
    (hg.integral_prod_left' (μ := μ)).aestronglyMeasurable
  have ha := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hb)
  filter_upwards [ha] with y hy
  change ∀ᵐ x ∂μ, ‖g (x, y)‖ ≤ B y at hy
  have hi := norm_integral_le_of_norm_le_const hy
  exact hi.trans_eq (mul_comm _ _)

theorem integral_coeFn_ae (v : X → Lp E 2 ν) (hv : Integrable v μ)
    (g : X × Y → E) (hg : StronglyMeasurable g)
    (hvg : ∀ᵐ x ∂μ, v x =ᵐ[ν] fun y => g (x, y))
    (B : Y → ℝ) (hB : MemLp B 2 ν)
    (hb : ∀ᵐ p ∂μ.prod ν, ‖g p‖ ≤ B p.2) :
    (∫ x, v x ∂μ) =ᵐ[ν] fun y => ∫ x, g (x, y) ∂μ := by
  let W := (column_memLp g hg B hB hb).toLp (fun y => ∫ x, g (x, y) ∂μ)
  have he : (∫ x, v x ∂μ) = W := BochnerL2Fubini.integral_eq_of_slices v hv g
    hg.aestronglyMeasurable hvg B hB hb W (MemLp.coeFn_toLp _)
  rw [he]
  exact MemLp.coeFn_toLp _

end OperatorDerivativeRewrite.Foundation.BochnerL2MajorantRealization
