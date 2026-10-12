import Foundation.ProductL2Curry

/-! Surjectivity of the product/Bochner L2 isometry, proved by simple-field density. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.ProductL2Curry
variable {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]

omit [SFinite μ] in
theorem productTensor_memLp (a : Lp ℝ 2 μ) (v : Lp E 2 ν) :
    MemLp (fun z : X × Y => a z.1 • v z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((Lp.stronglyMeasurable a).comp_measurable measurable_fst).smul
      ((Lp.stronglyMeasurable v).comp_measurable measurable_snd)).aestronglyMeasurable).mpr
  change Integrable (fun z : X × Y => ‖a z.1 • v z.2‖ ^ 2) (μ.prod ν)
  simpa only [Pi.smul_apply, Function.comp_apply, norm_smul, mul_pow] using
    (Lp.memLp a).norm.integrable_sq.mul_prod (Lp.memLp v).norm.integrable_sq

def productTensor (a : Lp ℝ 2 μ) (v : Lp E 2 ν) : Lp E 2 (μ.prod ν) :=
  (productTensor_memLp μ ν a v).toLp _

omit [SFinite μ] in
theorem productTensor_coeFn (a : Lp ℝ 2 μ) (v : Lp E 2 ν) :
    productTensor μ ν a v =ᵐ[μ.prod ν] fun z => a z.1 • v z.2 := MemLp.coeFn_toLp _

variable [SecondCountableTopology (Lp E 2 ν)]

theorem curry_productTensor (a : Lp ℝ 2 μ) (v : Lp E 2 ν) :
    curry μ ν (productTensor μ ν a v) = BochnerClosedOperator.tensor μ a v := by
  apply Lp.ext
  filter_upwards [curry_coeFn μ ν (productTensor μ ν a v),
    BochnerClosedOperator.tensor_coeFn μ a v,
    ae_ae_of_ae_prod (productTensor_coeFn μ ν a v)] with x hx ht hp
  rw [ht]
  apply Lp.ext
  filter_upwards [hx, hp, Lp.coeFn_smul (a x) v] with y hy hp hs
  simp only [hy, hp, hs, Pi.smul_apply]

theorem curry_surjective [CompleteSpace E] : Function.Surjective (curryIsometry μ ν (E := E)) := by
  let R := (curryIsometry μ ν (E := E)).toLinearMap.range
  have hc : IsClosed (R : Set (Lp (Lp E 2 ν) 2 μ)) :=
    (curryIsometry μ ν).isometry.isClosedEmbedding.isClosed_range
  have hr : ∀ f : Lp (Lp E 2 ν) 2 μ, f ∈ R := by
    apply Lp.induction (by simp) (fun f => f ∈ R)
    · intro v s hs hfin
      change indicatorConstLp 2 hs hfin.ne v ∈ R
      rw [indicatorConstLp_eq_toSpanSingleton_compLp]
      exact ⟨productTensor μ ν (indicatorConstLp 2 hs hfin.ne (1 : ℝ)) v,
        curry_productTensor μ ν _ v⟩
    · intro f g hf hg hd hfr hgr
      exact R.add_mem hfr hgr
    · exact hc
  exact hr

/-- A genuine onto isometry, with no representation or density assumptions. -/
def curryEquiv [CompleteSpace E] : Lp E 2 (μ.prod ν) ≃ₗᵢ[ℝ] Lp (Lp E 2 ν) 2 μ :=
  LinearIsometryEquiv.ofSurjective (curryIsometry μ ν) (curry_surjective μ ν)

theorem curryEquiv_coeFn [CompleteSpace E] (f : Lp E 2 (μ.prod ν)) :
    ∀ᵐ x ∂μ, curryEquiv μ ν f x =ᵐ[ν] fun y => f (x, y) := curry_coeFn μ ν f

theorem curryEquiv_symm_coeFn [CompleteSpace E] (u : Lp (Lp E 2 ν) 2 μ) :
    ∀ᵐ x ∂μ, u x =ᵐ[ν] fun y => (curryEquiv μ ν).symm u (x, y) := by
  have h := curryEquiv_coeFn μ ν ((curryEquiv μ ν).symm u)
  rwa [LinearIsometryEquiv.apply_symm_apply] at h

end OperatorDerivativeRewrite.Foundation.ProductL2Curry
