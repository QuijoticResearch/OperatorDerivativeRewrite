import Foundation.PhysicalTorusWaveSemigroup
import Foundation.WavePhysicalFourierBridge
/-! Exact coefficient, norm, generator and integrated energy bridge between
finite Laurent Fourier algebra and actual unit-torus Haar L². The earlier
box-average model uses period 2π, whereas the Haar torus here uses period one.
The bridge is by matching Fourier modes and energies; it does not claim a
pointwise scaling-map or Markov-process theorem. -/
open MeasureTheory Filter Set AddCircle
open scoped Topology NNReal ComplexConjugate InnerProductSpace
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.WaveTorusCoreBridge
open FiniteFourierDifferentialTrace FiniteFourierSynthesis
open PhysicalTorusWaveSemigroup

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def lift (f : Fourier) : E :=
  ∑ k ∈ f.coeff.support, f.coeff k • basis k

theorem repr_lift (f : Fourier) (k : Wave) :
    basis.repr (lift f) k = f.coeff k := by
  classical
  simp only [lift,map_sum,map_smul,HilbertBasis.repr_self,
    lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply]
  by_cases hk : f.coeff k = 0 <;> simp [Pi.single_apply,hk]

theorem lift_coeff (f : Fourier) (k : Wave) :
    UnitAddTorus.mFourierCoeff (lift f) k = f.coeff k := by
  simpa only [PhysicalTorusWaveSemigroup.basis,UnitAddTorus.mFourierBasis_repr] using
    repr_lift f k

theorem lift_injective : Function.Injective lift := by
  intro f g h
  ext k
  calc
    f.coeff k = UnitAddTorus.mFourierCoeff (lift f) k := (lift_coeff f k).symm
    _ = UnitAddTorus.mFourierCoeff (lift g) k := by rw [h]
    _ = g.coeff k := lift_coeff g k

theorem generator_coeff (a : Wave → ℝ) (f : Fourier) (k : Wave) :
    (FiniteStableGamma.Core.generator a f).coeff k = -(a k : ℂ) * f.coeff k := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf,hg,mul_add]
  | single l c =>
    by_cases h : l = k
    · subst l
      simp [FiniteStableGamma.Core.generator_single]
    · simp [FiniteStableGamma.Core.generator_single,Ne.symm h]

theorem lift_anisotropic_generator (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (f : Fourier) :
    Tendsto (PhysicalTorusWaveSemigroup.slope
        (WaveDiagonalSemigroup.rate a γ ha) (lift f)) (𝓝[>] 0)
      (𝓝 (lift (FiniteStableGamma.Core.generator
        (AnisotropicStableGamma.anisotropicSymbol a γ) f))) := by
  apply (PhysicalTorusWaveSemigroup.anisotropic_generator_iff a γ ha _ _).mpr
  intro k
  rw [lift_coeff,lift_coeff,generator_coeff]

theorem physical_inner_lift (f g : Fourier) :
    (∫ t, conj ((lift f) t) * (lift g) t) =
      ∑ k ∈ f.coeff.support, conj (f.coeff k) * g.coeff k := by
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (lift f) (lift g)
  simp only [lift_coeff] at h
  rw [← h.tsum_eq]
  exact tsum_eq_sum (s := f.coeff.support) (fun k hk => by
    have hc : f.coeff k = 0 := by
      simpa only [Finsupp.mem_support_iff, ne_eq, not_not] using hk
    simp [hc])

theorem physical_box_generator_energy (a : Wave → ℝ) (f : Fourier) :
    -(∫ t, conj ((lift f) t) *
      (lift (FiniteStableGamma.Core.generator a f)) t) =
      -FiniteFourierTorusAverage.boxAverage (fun x =>
        conj (synthesis x f) * synthesis x (FiniteStableGamma.Core.generator a f)) := by
  rw [physical_inner_lift,WavePhysicalFourierBridge.box_generator_energy_all]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [generator_coeff]
  ring

theorem physical_gamma1_energy (a : Wave → ℝ) (ha0 : a 0 = 0)
    (f : Fourier) :
    FiniteFourierTorusAverage.boxAverage (fun x =>
      synthesis x (FiniteStableGamma.Core.gammaIter a 1 f f)) =
      -(∫ t, conj ((lift f) t) *
        (lift (FiniteStableGamma.Core.generator a f)) t) := by
  exact (WavePhysicalFourierBridge.box_gamma1_energy a ha0 f).trans
    (physical_box_generator_energy a f).symm

theorem physical_norm_box_parseval (f : Fourier) :
    ((‖lift f‖ : ℂ)^2) =
      FiniteFourierTorusAverage.boxAverage (fun x =>
        conj (synthesis x f) * synthesis x f) := by
  calc
    ((‖lift f‖ : ℂ)^2) = ⟪lift f, lift f⟫_ℂ :=
      (inner_self_eq_norm_sq_to_K (lift f)).symm
    _ = ∫ t, conj ((lift f) t) * (lift f) t := by
      simp only [L2.inner_def,RCLike.inner_apply,mul_comm]
    _ = _ := by rw [physical_inner_lift,WavePhysicalFourierBridge.box_parseval_all]

end OperatorDerivativeRewrite.Foundation.WaveTorusCoreBridge
