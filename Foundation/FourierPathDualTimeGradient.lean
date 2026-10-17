import Foundation.FourierPathDualTimeSeries
import Foundation.FourierPathDualFrechet
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A genuine, uniquely representing Bochner time-gradient density on completed path tests. -/
noncomputable section
open MeasureTheory
open scoped lp NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.FourierPathDualTimeGradient
open L1SeriesSynthesis HigherHeatDyadicLaws HigherHeatFourierBanach
open FourierPathDualControls BochnerDualControlPairing FourierPathDualGradient

variable (levels : ℕ → ℕ) (ξ : (i : ℕ) → Grid (levels i))

theorem quotient_norm : ‖((kernel levels ξ).mkQL : Coeff →L[ℂ] TestSpace levels ξ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro a
  simp only [one_mul]
  exact Submodule.Quotient.norm_mk_le (kernel levels ξ) a

def coefficientField (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    Coeff →L[ℂ] BochnerDualControlPairing.Field (TestSpace levels ξ) m :=
  ((kernel levels ξ).mkQL.compLpL (HigherHeatLpControls.power m) volume).comp (FourierPathDualTimeSeries.series levels ξ m T hT)

theorem coefficientField_bound (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    ‖coefficientField levels ξ m T hT‖ ≤ 1+(T:ℝ)⁻¹ := by
  calc
    _ ≤ ‖(kernel levels ξ).mkQL.compLpL (HigherHeatLpControls.power m) (volume : Measure ℝ)‖ *
        ‖FourierPathDualTimeSeries.series levels ξ m T hT‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1*(1+(T:ℝ)⁻¹) := mul_le_mul
      ((ContinuousLinearMap.norm_compLpL_le (p := HigherHeatLpControls.power m)
        (μ := (volume : Measure ℝ)) (kernel levels ξ).mkQL).trans (quotient_norm levels ξ))
      (FourierPathDualTimeSeries.series_bound levels ξ m T hT) (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem coefficientField_pairing (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (a : Coeff) (u : Control m) :
    pairing (TestSpace levels ξ) m u (coefficientField levels ξ m T hT a) =
      (kernel levels ξ).mkQ (FourierPathDualGradientSeries.family levels ξ m T hT a u) := by
  have hh := pairing_compLp Coeff m ((kernel levels ξ).mkQL.restrictScalars ℝ) u
    (FourierPathDualTimeSeries.series levels ξ m T hT a)
  change pairing (TestSpace levels ξ) m u (coefficientField levels ξ m T hT a) =
    (kernel levels ξ).mkQ (pairing Coeff m u (FourierPathDualTimeSeries.series levels ξ m T hT a)) at hh
  rwa [FourierPathDualTimeSeries.series_pairing] at hh

theorem kernel_le_field (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    kernel levels ξ ≤ (coefficientField levels ξ m T hT).ker := by
  intro a ha
  apply annihilator_zero (TestSpace levels ξ) m
  intro u
  change pairing (TestSpace levels ξ) m u (coefficientField levels ξ m T hT a) = 0
  rw [coefficientField_pairing levels ξ m T hT a u]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (FourierPathDualGradientSeries.family_preserves_kernel levels ξ m T hT a ha u)

def timeGradient (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) :
    TestSpace levels ξ →L[ℂ] BochnerDualControlPairing.Field (TestSpace levels ξ) m :=
  (kernel levels ξ).liftQL (coefficientField levels ξ m T hT) (kernel_le_field levels ξ m T hT)

theorem timeGradient_bound (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T) (q : TestSpace levels ξ) :
    ‖timeGradient levels ξ m T hT q‖ ≤ (1+(T:ℝ)⁻¹)*‖q‖ := by
  let C := 1+(T:ℝ)⁻¹
  have hC : 0 < C := by dsimp [C]; positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,ha,hna⟩ := Submodule.Quotient.norm_mk_lt q (div_pos hε hC)
  have he : timeGradient levels ξ m T hT q = coefficientField levels ξ m T hT a := by
    rw [← ha]; rfl
  rw [he]
  calc
    _ ≤ C*‖a‖ := (coefficientField levels ξ m T hT).le_of_opNorm_le
      (coefficientField_bound levels ξ m T hT) a
    _ ≤ C*‖q‖+ε := by
      have hh := mul_lt_mul_of_pos_left hna hC
      have hc : C*(ε/C)=ε := by field_simp
      nlinarith

theorem timeGradient_pairing (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    pairing (TestSpace levels ξ) m u (timeGradient levels ξ m T hT q) =
      gradient levels ξ m T hT q u := by
  obtain ⟨a,rfl⟩ := (kernel levels ξ).mkQ_surjective q
  rw [gradient_mk]
  exact coefficientField_pairing levels ξ m T hT a u

theorem timeGradient_integral (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    (∫ s, u s • timeGradient levels ξ m T hT q s) = gradient levels ξ m T hT q u := by
  rw [← BochnerDualControlPairing.pairing_integral]
  exact timeGradient_pairing levels ξ m T hT q u

theorem timeGradient_unique (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (f : BochnerDualControlPairing.Field (TestSpace levels ξ) m)
    (hf : ∀ u : Control m, pairing (TestSpace levels ξ) m u f = gradient levels ξ m T hT q u) :
    f = timeGradient levels ξ m T hT q := by
  apply pairing_injective (TestSpace levels ξ) m
  ext u
  exact (hf u).trans (timeGradient_pairing levels ξ m T hT q u).symm

theorem orbit_density_derivative (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (u : Control m) :
    HasFDerivAt (fun v => HigherHeatFourierTranslations.translation levels ξ (direction m v)
      (HigherHeatFourierPathSemigroup.evolution levels ξ m h.out T q))
      ((pairing (TestSpace levels ξ) m).flip (timeGradient levels ξ m T hT
        (HigherHeatFourierTranslations.translation levels ξ (direction m u) q))) u := by
  have hd := FourierPathDualFrechet.orbit_hasFDerivAt levels ξ m T hT q u
  convert hd using 1
  ext v
  exact timeGradient_pairing levels ξ m T hT _ v

def realizedField (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : HigherHeatContinuousCylinders.Path) :
    BochnerDualControlPairing.Field ℂ m :=
  ((BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)).compLpL
    (HigherHeatLpControls.power m) volume (timeGradient levels ξ m T hT q)

theorem realizedField_pairing (m : ℕ) [Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : HigherHeatContinuousCylinders.Path) (u : Control m) :
    pairing ℂ m u (realizedField levels ξ m T hT q ω) =
      realize levels ξ (gradient levels ξ m T hT q u) ω := by
  have hh := pairing_compLp (TestSpace levels ξ) m
    (((BoundedContinuousFunction.evalCLM ℂ ω).comp (realize levels ξ)).restrictScalars ℝ) u
    (timeGradient levels ξ m T hT q)
  change pairing ℂ m u (realizedField levels ξ m T hT q ω) =
    realize levels ξ (pairing (TestSpace levels ξ) m u (timeGradient levels ξ m T hT q)) ω at hh
  rwa [timeGradient_pairing] at hh

theorem realized_density_derivative (m : ℕ) [h : Fact (0 < m)] (T : ℝ≥0) (hT : 0 < T)
    (q : TestSpace levels ξ) (ω : HigherHeatContinuousCylinders.Path) (u : Control m) :
    HasFDerivAt (fun v => realize levels ξ
      (HigherHeatFourierPathSemigroup.evolution levels ξ m h.out T q)
      (HigherHeatFourierTranslations.addPath (direction m v) ω))
      ((pairing ℂ m).flip (realizedField levels ξ m T hT
        (HigherHeatFourierTranslations.translation levels ξ (direction m u) q) ω)) u := by
  have hd := FourierPathDualFrechet.realized_hasFDerivAt levels ξ m T hT q ω u
  convert hd using 1
  ext v
  exact realizedField_pairing levels ξ m T hT _ ω v

def expectationField (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) :
    BochnerDualControlPairing.Field ℂ m :=
  (expectation levels ξ k hk H hH).compLpL (HigherHeatLpControls.power m) volume
    (timeGradient levels ξ m T hT q)

theorem expectationField_pairing (m : ℕ) [Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (u : Control m) :
    pairing ℂ m u (expectationField levels ξ m k hk T H hT hH q) =
      expectation levels ξ k hk H hH (gradient levels ξ m T hT q u) := by
  have hh := pairing_compLp (TestSpace levels ξ) m
    ((expectation levels ξ k hk H hH).restrictScalars ℝ) u (timeGradient levels ξ m T hT q)
  change pairing ℂ m u (expectationField levels ξ m k hk T H hT hH q) =
    expectation levels ξ k hk H hH
      (pairing (TestSpace levels ξ) m u (timeGradient levels ξ m T hT q)) at hh
  rwa [timeGradient_pairing] at hh

theorem expectation_density_derivative (m : ℕ) [h : Fact (0 < m)] (k : ℕ) (hk : 0 < k)
    (T H : ℝ≥0) (hT : 0 < T) (hH : 0 < H) (q : TestSpace levels ξ) (u : Control m) :
    HasFDerivAt (fun v => expectation levels ξ k hk H hH
      (HigherHeatFourierTranslations.translation levels ξ (direction m v)
        (HigherHeatFourierPathSemigroup.evolution levels ξ m h.out T q)))
      ((pairing ℂ m).flip (expectationField levels ξ m k hk T H hT hH
        (HigherHeatFourierTranslations.translation levels ξ (direction m u) q))) u := by
  have hd := FourierPathDualFrechet.expectation_hasFDerivAt levels ξ m k hk T H hT hH q u
  convert hd using 1
  ext v
  exact expectationField_pairing levels ξ m k hk T H hT hH _ v

end OperatorDerivativeRewrite.Foundation.FourierPathDualTimeGradient
