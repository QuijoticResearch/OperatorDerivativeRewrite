import Foundation.FiniteHeatSquarePositivity
import Foundation.WaveTorusCoreBridge

/-! Exact finite-core intertwining with the completed Haar-L² torus
semigroup. The semigroup preserves almost-everywhere nonnegativity of finite
Fourier squares precisely under the mixed-stable active-axis criterion, and
fails it on an explicit square when an active exponent exceeds two. This
does not yet prove positivity on every nonnegative L² input. -/
open MeasureTheory AddCircle
open scoped NNReal ComplexConjugate BigOperators
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatSquareBridge
open FiniteFourierDifferentialTrace FiniteHeatSquarePositivity
open FiniteFourierReality FiniteStableGamma.Core FiniteStableGamma.ComplexEnergy
open FourierGammaCovariance FiniteSchoenberg FourierCovarianceCriterion
open PhysicalTorusWaveSemigroup WaveTorusCoreBridge

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem heatAction_coeff (ψ : Wave → ℝ) (t : ℝ) (f : Fourier) (k : Wave) :
    (heatAction ψ t f).coeff k = (Real.exp (-t*ψ k) : ℂ)*f.coeff k := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg => simp [hf,hg,mul_add]
  | single l c =>
    by_cases h : l = k
    · subst l
      simp [heatAction_single]
    · simp [heatAction_single,Ne.symm h]

theorem heatAction_zero (ψ : Wave → ℝ) (f : Fourier) :
    heatAction ψ 0 f = f := by
  ext k
  simp [heatAction_coeff]

theorem lift_heatAction (r : Wave → ℝ≥0) (t : ℝ≥0) (f : Fourier) :
    lift (heatAction (fun k => (r k : ℝ)) (t : ℝ) f) =
      evolution r t (lift f) := by
  apply basis.repr.injective
  ext k
  simp only [PhysicalTorusWaveSemigroup.basis, UnitAddTorus.mFourierBasis_repr]
  rw [lift_coeff, evolution_coeff, lift_coeff, heatAction_coeff]
  simp only [WaveDiagonalSemigroup.multiplier]
  ring

def torusSynthesis : Fourier →ₗ[ℂ] C(UnitAddTorus (Fin 3), ℂ) :=
  (Finsupp.linearCombination ℂ (fun k : Wave => UnitAddTorus.mFourier k)).comp
    (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem torusSynthesis_single (k : Wave) (c : ℂ) :
    torusSynthesis (AddMonoidAlgebra.single k c) = c • UnitAddTorus.mFourier k := by
  simp [torusSynthesis,Finsupp.linearCombination_single]

theorem torusSynthesis_toLp (f : Fourier) :
    ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 3))) ℂ
      (torusSynthesis f) = lift f := by
  classical
  simp only [torusSynthesis, LinearMap.comp_apply]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smul, lift, PhysicalTorusWaveSemigroup.basis,
    UnitAddTorus.coe_mFourierBasis, UnitAddTorus.mFourierLp]
  have hcoeff : (AddMonoidAlgebra.coeffLinearEquiv ℂ) f = f.coeff := rfl
  change (∑ x ∈ ((AddMonoidAlgebra.coeffLinearEquiv ℂ) f).support,
      ((AddMonoidAlgebra.coeffLinearEquiv ℂ) f) x •
        (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 3))) ℂ)
          (UnitAddTorus.mFourier x)) = _
  rw [hcoeff]

theorem torus_heat_square_energy {ι : Type*} [Fintype ι]
    (ψ : Wave → ℝ) (t : ℝ) (k : ι → Wave) (c : ι → ℂ)
    (x : UnitAddTorus (Fin 3)) :
    torusSynthesis (heatAction ψ t
      (reflection (∑ i, AddMonoidAlgebra.single (k i) (c i)) *
        (∑ i, AddMonoidAlgebra.single (k i) (c i)))) x =
      energy (fun i j => Real.exp (-t*ψ (k j-k i)))
        (fun i => c i * UnitAddTorus.mFourier (k i) x) := by
  change torusSynthesis (heatAction ψ t
    (gammaIter ψ 0 (∑ i, AddMonoidAlgebra.single (k i) (c i))
      (∑ i, AddMonoidAlgebra.single (k i) (c i)))) x = _
  rw [gammaIter_finite]
  simp only [map_sum, heatAction_single, torusSynthesis_single,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  unfold energy
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [map_mul, sub_eq_add_neg, UnitAddTorus.mFourier_add,
    UnitAddTorus.mFourier_neg]
  ring

theorem torus_heat_square_nonnegative (ψ : Wave → ℝ)
    (hψ : CovarianceSymbol ψ) (t : ℝ) (ht : 0 ≤ t)
    (f : Fourier) (x : UnitAddTorus (Fin 3)) :
    (torusSynthesis (heatAction ψ t (reflection f * f)) x).im = 0 ∧
      0 ≤ (torusSynthesis (heatAction ψ t (reflection f * f)) x).re := by
  classical
  have hf : (∑ k : f.coeff.support,
      AddMonoidAlgebra.single k.val (f.coeff k.val)) = f :=
    (Finset.sum_attach f.coeff.support
      (fun k => AddMonoidAlgebra.single k (f.coeff k))).trans
        (AddMonoidAlgebra.sum_coeff_single f)
  rw [← hf]
  rw [torus_heat_square_energy]
  exact energy_nonnegative _
    (heat_multiplier_psd_of_covariance ψ hψ t ht
      (fun k : f.coeff.support => k.val)) _

theorem torus_square_nonnegative (f : Fourier) (x : UnitAddTorus (Fin 3)) :
    (torusSynthesis (reflection f * f) x).im = 0 ∧
      0 ≤ (torusSynthesis (reflection f * f) x).re := by
  have h := torus_heat_square_nonnegative (fun _ => 0)
    AnisotropicStableGamma.covariance_zero 0 (le_refl 0) f x
  simpa only [heatAction_zero] using h

theorem torus_heat_square_real_energy_at_zero {ι : Type} [Fintype ι]
    (ψ : Wave → ℝ) (t : ℝ) (k : ι → Wave) (w : ι → ℝ) :
    (torusSynthesis (heatAction ψ t
      (reflection (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ)) *
        (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ)))) (0 : UnitAddTorus (Fin 3))).re =
      expEnergy (fun i j => ψ (k j-k i)) w t := by
  rw [torus_heat_square_energy]
  simp [energy, expEnergy, UnitAddTorus.mFourier, ← Complex.ofReal_exp]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem continuous_negative_not_ae_nonnegative
    (g : C(UnitAddTorus (Fin 3), ℂ)) (x₀ : UnitAddTorus (Fin 3))
    (hneg : (g x₀).re < 0) :
    ¬ ∀ᵐ x : UnitAddTorus (Fin 3)
        ∂(volume : Measure (UnitAddTorus (Fin 3))), 0 ≤ (g x).re := by
  intro h
  let U : Set (UnitAddTorus (Fin 3)) := {x | (g x).re < 0}
  have hU : IsOpen U := isOpen_lt (Complex.continuous_re.comp g.continuous) continuous_const
  have hnull : (volume : Measure (UnitAddTorus (Fin 3))) U = 0 := by
    simpa only [U, not_le] using (ae_iff.mp h)
  exact (ne_of_gt (hU.measure_pos _ ⟨x₀, hneg⟩)) hnull

theorem physical_evolution_negative_of_positive_symbol_energy
    (r : Wave → ℝ≥0) (k : Fin 3 → Wave) (w : Fin 3 → ℝ)
    (hw : ∑ i, w i = 0)
    (hd : 0 < AnchoredCovariance.energy
      (fun i j => (r (k j-k i) : ℝ)) w) :
    ∃ t : ℝ≥0, 0 < t ∧
      ¬ ∀ᵐ x : UnitAddTorus (Fin 3)
          ∂(volume : Measure (UnitAddTorus (Fin 3))),
        0 ≤ ((evolution r t
          (lift (reflection (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ)) *
            (∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ))))) x).re := by
  obtain ⟨s, hs, hn⟩ := FiniteBochnerObstruction.expEnergy_eventually_negative
    (fun i j => (r (k j-k i) : ℝ)) w hw hd
  let f : Fourier := ∑ i, AddMonoidAlgebra.single (k i) (w i : ℂ)
  let g := torusSynthesis (heatAction (fun k => (r k : ℝ)) s (reflection f * f))
  have hg : (g (0 : UnitAddTorus (Fin 3))).re < 0 := by
    simpa only [g, f] using
      (show (g (0 : UnitAddTorus (Fin 3))).re =
        expEnergy (fun i j => (r (k j-k i) : ℝ)) w s from
        torus_heat_square_real_energy_at_zero _ s k w).trans_lt hn
  let t : ℝ≥0 := ⟨s, hs.le⟩
  refine ⟨t, by exact hs, ?_⟩
  have he : evolution r t (lift (reflection f * f)) =
      (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 3))) ℂ) g := by
    rw [← lift_heatAction]
    change lift (heatAction (fun k => (r k : ℝ)) s (reflection f * f)) = _
    exact (torusSynthesis_toLp _).symm
  intro hout
  rw [he] at hout
  apply continuous_negative_not_ae_nonnegative g 0 hg
  filter_upwards [hout, ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2)
      (volume : Measure (UnitAddTorus (Fin 3))) g] with x hx heq
  simpa only [heq] using hx

theorem anisotropic_physical_evolution_not_positive_above_two
    (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hγ0 : ∀ j, 0 < γ j) (j : Fin 3)
    (haj : 0 < a j) (hγgt : 2 < γ j) :
    ∃ t : ℝ≥0, 0 < t ∧
      ¬ ∀ᵐ x : UnitAddTorus (Fin 3)
          ∂(volume : Measure (UnitAddTorus (Fin 3))),
        0 ≤ ((evolution (WaveDiagonalSemigroup.rate a γ ha) t
          (lift (reflection (∑ i, AddMonoidAlgebra.single
            (AnisotropicMixedThreshold.axisTriple j i)
            (AnisotropicStableEndpoint.tripleWeights i : ℂ)) *
            (∑ i, AddMonoidAlgebra.single
              (AnisotropicMixedThreshold.axisTriple j i)
              (AnisotropicStableEndpoint.tripleWeights i : ℂ))))) x).re := by
  have hp : (4 : ℝ) < 2^(γ j) := by
    have hh := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hγgt
    norm_num at hh
    exact hh
  have hd : 0 < AnchoredCovariance.energy
      (fun i l => ((WaveDiagonalSemigroup.rate a γ ha
        (AnisotropicMixedThreshold.axisTriple j l -
          AnisotropicMixedThreshold.axisTriple j i) : ℝ)))
      AnisotropicStableEndpoint.tripleWeights := by
    change 0 < AnchoredCovariance.energy
      (fun i l => AnisotropicStableGamma.anisotropicSymbol a γ
        (AnisotropicMixedThreshold.axisTriple j l -
          AnisotropicMixedThreshold.axisTriple j i))
      AnisotropicStableEndpoint.tripleWeights
    rw [AnisotropicMixedThreshold.mixed_triple_energy a γ hγ0 j]
    exact mul_pos haj (by linarith)
  exact physical_evolution_negative_of_positive_symbol_energy
    (WaveDiagonalSemigroup.rate a γ ha)
    (AnisotropicMixedThreshold.axisTriple j)
    AnisotropicStableEndpoint.tripleWeights
    AnisotropicStableEndpoint.triple_sum hd

theorem physical_square_input_ae (f : Fourier) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂(volume : Measure (UnitAddTorus (Fin 3))),
      ((lift (reflection f * f)) x).im = 0 ∧
        0 ≤ ((lift (reflection f * f)) x).re := by
  rw [← torusSynthesis_toLp]
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2)
      (volume : Measure (UnitAddTorus (Fin 3)))
      (torusSynthesis (reflection f * f))] with x hx
  rw [hx]
  exact torus_square_nonnegative f x

theorem physical_evolution_square_ae (r : Wave → ℝ≥0)
    (hr : CovarianceSymbol (fun k => (r k : ℝ)))
    (t : ℝ≥0) (f : Fourier) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂(volume : Measure (UnitAddTorus (Fin 3))),
      ((evolution r t (lift (reflection f * f))) x).im = 0 ∧
        0 ≤ ((evolution r t (lift (reflection f * f))) x).re := by
  have he := (lift_heatAction r t (reflection f * f)).symm
  have hp := torusSynthesis_toLp
    (heatAction (fun k => (r k : ℝ)) (t : ℝ) (reflection f * f))
  rw [he, ← hp]
  filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (E := ℂ) (p := 2)
      (volume : Measure (UnitAddTorus (Fin 3)))
      (torusSynthesis (heatAction (fun k => (r k : ℝ)) (t : ℝ)
        (reflection f * f)))] with x hx
  rw [hx]
  exact torus_heat_square_nonnegative _ hr t t.coe_nonneg f x

theorem anisotropic_physical_evolution_square_ae (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hγ0 : ∀ j, 0 < γ j)
    (hactive : ∀ j, 0 < a j → γ j ≤ 2)
    (t : ℝ≥0) (f : Fourier) :
    ∀ᵐ x : UnitAddTorus (Fin 3) ∂(volume : Measure (UnitAddTorus (Fin 3))),
      ((evolution (WaveDiagonalSemigroup.rate a γ ha) t
        (lift (reflection f * f))) x).im = 0 ∧
      0 ≤ ((evolution (WaveDiagonalSemigroup.rate a γ ha) t
        (lift (reflection f * f))) x).re := by
  apply physical_evolution_square_ae
  change CovarianceSymbol (AnisotropicStableGamma.anisotropicSymbol a γ)
  exact AnisotropicMixedThreshold.anisotropic_covariance_of_positive_axes
    a γ ha hγ0 hactive

theorem anisotropic_physical_square_positive_iff_active
    (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hγ0 : ∀ j, 0 < γ j) :
    (∀ (t : ℝ≥0) (f : Fourier),
      ∀ᵐ x : UnitAddTorus (Fin 3)
          ∂(volume : Measure (UnitAddTorus (Fin 3))),
        0 ≤ ((evolution (WaveDiagonalSemigroup.rate a γ ha) t
          (lift (reflection f * f))) x).re) ↔
      ∀ j, 0 < a j → γ j ≤ 2 := by
  constructor
  · intro h j hj
    by_contra hn
    obtain ⟨t, ht, hneg⟩ :=
      anisotropic_physical_evolution_not_positive_above_two
        a γ ha hγ0 j hj (lt_of_not_ge hn)
    exact hneg (h t (∑ i, AddMonoidAlgebra.single
      (AnisotropicMixedThreshold.axisTriple j i)
      (AnisotropicStableEndpoint.tripleWeights i : ℂ)))
  · intro hactive t f
    filter_upwards [anisotropic_physical_evolution_square_ae
      a γ ha hγ0 hactive t f] with x hx
    exact hx.2

end OperatorDerivativeRewrite.Foundation.PhysicalHeatSquareBridge
