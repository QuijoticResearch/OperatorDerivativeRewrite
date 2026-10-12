import Foundation.ProductL2Sections
import Foundation.BochnerClosedOperator

/-! Actual Hilbert-valued product L2 and Bochner L2 identification. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ProductL2Curry
open ProductL2Sections
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
  [SecondCountableTopology (Lp E 2 ν)]

omit [MeasurableSpace X] [SFinite ν] [SecondCountableTopology (Lp E 2 ν)] in
theorem section_norm_sq (f : X × Y → E) (x : X)
    (hf : MemLp (fun y => f (x, y)) 2 ν) :
    ‖sectionL2 ν f x‖ ^ 2 = ∫ y, ‖f (x, y)‖ ^ 2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sectionL2_coeFn ν f x hf] with y hy
  rw [hy, real_inner_self_eq_norm_sq]

theorem section_memLp (f : Lp E 2 (μ.prod ν)) : MemLp (sectionL2 ν f) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm
    (sectionL2_stronglyMeasurable ν f (Lp.stronglyMeasurable f)).aestronglyMeasurable).mpr
  have hi := ((Lp.memLp f).norm.integrable_sq).integral_prod_left
  apply hi.congr
  filter_upwards [ae_memLp_sections ν μ f] with x hx
  exact (section_norm_sq ν f x hx).symm

def curry (f : Lp E 2 (μ.prod ν)) : Lp (Lp E 2 ν) 2 μ :=
  (section_memLp μ ν f).toLp _

theorem curry_coeFn (f : Lp E 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, curry μ ν f x =ᵐ[ν] fun y => f (x, y) := by
  filter_upwards [MemLp.coeFn_toLp (section_memLp μ ν f), ae_memLp_sections ν μ f]
    with x hx hm
  change curry μ ν f x = sectionL2 ν f x at hx
  rw [hx]
  exact sectionL2_coeFn ν f x hm

theorem curry_norm (f : Lp E 2 (μ.prod ν)) : ‖curry μ ν f‖ = ‖f‖ := by
  have he : ‖curry μ ν f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq (x := f),
      L2.inner_def, L2.inner_def,
      integral_prod _ (L2.integrable_inner f f)]
    apply integral_congr_ae
    filter_upwards [curry_coeFn μ ν f] with x hx
    rw [L2.inner_def]
    exact integral_congr_ae (hx.mono fun y hy => congrArg (fun v : E => inner ℝ v v) hy)
  nlinarith [norm_nonneg (curry μ ν f), norm_nonneg f]

def curryLinear : Lp E 2 (μ.prod ν) →ₗ[ℝ] Lp (Lp E 2 ν) 2 μ where
  toFun := curry μ ν
  map_add' f g := by
    apply Lp.ext
    filter_upwards [curry_coeFn μ ν (f + g), curry_coeFn μ ν f, curry_coeFn μ ν g,
      Lp.coeFn_add (curry μ ν f) (curry μ ν g), ae_ae_of_ae_prod (Lp.coeFn_add f g)]
      with x hsum hf hg hout hin
    rw [hout]
    apply Lp.ext
    filter_upwards [hsum, hf, hg, hin, Lp.coeFn_add (curry μ ν f x) (curry μ ν g x)]
      with y hs hf hg hi he
    simp only [hs, he, Pi.add_apply, hf, hg, hi]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [curry_coeFn μ ν (c • f), curry_coeFn μ ν f,
      Lp.coeFn_smul c (curry μ ν f), ae_ae_of_ae_prod (Lp.coeFn_smul c f)]
      with x hsm hf hout hin
    change curry μ ν (c • f) x = (c • curry μ ν f) x
    rw [hout]
    apply Lp.ext
    filter_upwards [hsm, hf, hin, Lp.coeFn_smul c (curry μ ν f x)] with y hs hf hi he
    simp only [hs, he, Pi.smul_apply, hf, hi]

def curryIsometry : Lp E 2 (μ.prod ν) →ₗᵢ[ℝ] Lp (Lp E 2 ν) 2 μ where
  toLinearMap := curryLinear μ ν
  norm_map' := curry_norm μ ν

end OperatorDerivativeRewrite.Foundation.ProductL2Curry
