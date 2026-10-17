import Foundation.FiniteGammaSeed

/-! The full bounded finite test algebra is actually all of L2 of the uniform probability law. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace OperatorDerivativeRewrite.Foundation.FiniteGammaL2Algebra
open FiniteGammaSeed
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

abbrev BaseL2 := Lp ℝ 2 μ

theorem ae_iff_forall (p : State → Prop) : (∀ᵐ s ∂μ, p s) ↔ ∀ s, p s := by
  rw [μ, Measure.ae_ennreal_smul_measure_iff (by norm_num), Measure.ae_count_iff]

def toL2 (f : Algebra) : BaseL2 := (all_memLp f 2).toLp f

theorem toL2_coeFn (f : Algebra) : ∀ s, toL2 f s = f s :=
  (ae_iff_forall _).mp (MemLp.coeFn_toLp _)

def toL2Linear : Algebra →ₗ[ℝ] BaseL2 where
  toFun := toL2
  map_add' f g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (toL2 f) (toL2 g)] with s h
    rw [toL2_coeFn, h]
    change f s + g s = toL2 f s + toL2 g s
    rw [toL2_coeFn, toL2_coeFn]
  map_smul' r f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul r (toL2 f)] with s h
    rw [toL2_coeFn]
    change (r • f) s = (r • toL2 f) s
    rw [h]
    change r * f s = r * toL2 f s
    rw [toL2_coeFn]

theorem toL2_injective : Function.Injective toL2 := by
  intro f g h
  funext s
  rw [← toL2_coeFn f s, h, toL2_coeFn g s]

theorem toL2_surjective : Function.Surjective toL2 := by
  intro u
  refine ⟨fun s => u s, ?_⟩
  apply Lp.ext
  filter_upwards [] with s
  exact toL2_coeFn _ s

def algebraEquiv : Algebra ≃ₗ[ℝ] BaseL2 :=
  LinearEquiv.ofBijective toL2Linear ⟨toL2_injective, toL2_surjective⟩

theorem algebraEquiv_apply (f : Algebra) : algebraEquiv f = toL2 f := rfl

instance baseL2_finite : FiniteDimensional ℝ BaseL2 :=
  Module.Finite.of_surjective toL2Linear toL2_surjective

theorem bounded_dense_algebra :
    (∀ f : Algebra, MemLp f ∞ μ ∧ MemLp f 2 μ) ∧ DenseRange toL2 :=
  ⟨fun f => ⟨all_memLp f ∞, all_memLp f 2⟩, toL2_surjective.denseRange⟩

theorem actual_energy_tendsto_zero (f : ℕ → Algebra)
    (hf : Filter.Tendsto (fun n => toL2 (f n)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => expect (gamma (f n) (f n))) Filter.atTop (nhds 0) := by
  have hc : Continuous (algebraEquiv.symm : BaseL2 → Algebra) :=
    algebraEquiv.symm.toLinearMap.continuous_of_finiteDimensional
  have h := hc.tendsto 0 |>.comp hf
  have he (n : ℕ) : algebraEquiv.symm (toL2 (f n)) = f n :=
    algebraEquiv.symm_apply_apply (f n)
  have hr : Filter.Tendsto f Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, he, map_zero] using h
  exact energy_tendsto_zero f hr

theorem form_closable (f : ℕ → Algebra)
    (hf : Filter.Tendsto (fun n => toL2 (f n)) Filter.atTop (nhds 0))
    (_hEnergyCauchy : Filter.Tendsto
      (fun p : ℕ × ℕ => expect (gamma (f p.1 - f p.2) (f p.1 - f p.2)))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => expect (gamma (f n) (f n))) Filter.atTop (nhds 0) :=
  actual_energy_tendsto_zero f hf

end OperatorDerivativeRewrite.Foundation.FiniteGammaL2Algebra
