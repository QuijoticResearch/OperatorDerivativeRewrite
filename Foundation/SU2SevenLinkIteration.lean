import Foundation.SU2SevenLinkL2Transfer

/-! Iteration of the actual gauge-invariant stationary seven-link transfer.
The small independent spatial-tilt restriction is retained. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.SU2SevenLinkIteration
open SU2SevenLinkTransfer SU2SevenLinkGroundTransform SU2SevenLinkL2Transfer
open SU2SevenLinkVacuum SU2WilsonConvolution
variable {β t : ℝ} (d : GroundData β t)

abbrev steps := SelfAdjointContractionIteration.steps (operator d)

theorem iteration_from_one_step (f : StateL2 d) (q : ℝ)
    (hq : q*inner ℝ f f ≤ inner ℝ (operator d f) f) (n : ℕ) :
    (1-(n:ℝ)*(1-q))*inner ℝ f f ≤ inner ℝ (steps d n f) f := by
  have he := SelfAdjointContractionIteration.lag_lower (operator d)
    (operator_contraction d) (operator_symmetric d) n f
  have hD : SelfAdjointContractionIteration.dissipation (operator d) f ≤ (1-q)*inner ℝ f f := by
    unfold SelfAdjointContractionIteration.dissipation
    linarith
  have hn := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg n)
  nlinarith

theorem realized_iteration_interval (β : ℝ) (hc : coefficient β ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < δ →
      let v := (data β t).evenized
      let f := v.observable (SU2SevenLinkSpatialSeparation.oddA β) (SU2SevenLinkSpatialSeparation.oddB β)
      let F := probe v (SU2SevenLinkSpatialSeparation.oddA β) (SU2SevenLinkSpatialSeparation.oddB β)
      (∀ (g : Fin 6 → QuaternionSU2Representation.SU2) s,f (gaugeAction g s)=f s) ∧
      (∫ s,F s ∂v.stationary)=0 ∧ 0 < inner ℝ F F ∧
      ∀ n : ℕ, (1-(n:ℝ)*(1-coefficient β^4))*inner ℝ F F ≤ inner ℝ (steps v n F) F ∧
        inner ℝ (steps v n F) F ≤ inner ℝ F F ∧
        inner ℝ (steps v n F) F=∫ s,f s*nativeSteps v n f s ∂v.stationary := by
  obtain ⟨δ,hδ,hδ1,hall⟩ := gauge_invariant_stationary_obstruction_interval β hc
  refine ⟨δ,hδ,hδ1,?_⟩
  intro t ht htδ
  let v := (data β t).evenized
  let A := SU2SevenLinkSpatialSeparation.oddA β
  let B := SU2SevenLinkSpatialSeparation.oddB β
  have he := hall t ht htδ
  refine ⟨he.1,probe_mean v A B (data β t).evenized_even,?_,?_⟩
  · rw [probe_square]
    exact he.2.2.1
  · intro n
    have h1 : coefficient β^4*inner ℝ (probe v A B) (probe v A B) ≤
        inner ℝ (operator v (probe v A B)) (probe v A B) := by
      rw [probe_square,probe_lag]
      exact ((lt_div_iff₀ he.2.2.1).mp he.2.2.2).le
    refine ⟨iteration_from_one_step v _ _ h1 n,
      SelfAdjointContractionIteration.lag_upper (operator v) (operator_contraction v)
        (operator_symmetric v) n _,?_⟩
    exact steps_pairing v n _ (v.observable_memLp A B) (v.observable_measurable A B)
      _ (v.observable_bound A B)

/-- Even allowing an arbitrary large-coupling cutoff, no fixed number of
actual Markov steps supplies a parameter-uniform subunit covariance factor.
The positive spatial tilt is chosen independently and may depend on beta. -/
theorem no_uniform_fixed_steps (n : ℕ) (q R : ℝ) (hq : q < 1) :
    ∃ β t : ℝ, R < β ∧ 0 < t ∧ t ≤ 1 ∧
      let v := (data β t).evenized
      let f := v.observable (SU2SevenLinkSpatialSeparation.oddA β) (SU2SevenLinkSpatialSeparation.oddB β)
      (∀ (g : Fin 6 → QuaternionSU2Representation.SU2) s,f (gaugeAction g s)=f s) ∧
      (∫ s,f s ∂v.stationary)=0 ∧ 0 < (∫ s,(f s)^2 ∂v.stationary) ∧
      q < (∫ s,f s*nativeSteps v n f s ∂v.stationary)/(∫ s,(f s)^2 ∂v.stationary) := by
  let r := (q+(n:ℝ))/((n:ℝ)+1)
  have hn : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hr : r < 1 := (div_lt_one hn).mpr (by linarith)
  obtain ⟨β,t,hβ,ht,ht1,hg,hm,hv,hl⟩ := no_uniform_stationary_contraction r R hr
  let v := (data β t).evenized
  let A := SU2SevenLinkSpatialSeparation.oddA β
  let B := SU2SevenLinkSpatialSeparation.oddB β
  have hV : 0 < inner ℝ (probe v A B) (probe v A B) := by rw [probe_square]; exact hv
  have h1 : r*inner ℝ (probe v A B) (probe v A B) ≤
      inner ℝ (operator v (probe v A B)) (probe v A B) := by
    rw [probe_square,probe_lag]
    exact ((lt_div_iff₀ hv).mp hl).le
  have hcoef : q < 1-(n:ℝ)*(1-r) := by
    have he : 1-(n:ℝ)*(1-r)-q=(1-q)/((n:ℝ)+1) := by dsimp [r]; field_simp; ring
    have hp := div_pos (sub_pos.mpr hq) hn
    linarith
  have hlow := iteration_from_one_step v _ r h1 n
  have hpos := mul_pos (sub_pos.mpr hcoef) hV
  have hgt : q*inner ℝ (probe v A B) (probe v A B) <
      inner ℝ (steps v n (probe v A B)) (probe v A B) := by nlinarith
  rw [probe_square] at hgt
  have hNative := steps_pairing v n _ (v.observable_memLp A B) (v.observable_measurable A B)
    _ (v.observable_bound A B)
  change inner ℝ (steps v n (probe v A B)) (probe v A B)=
    ∫ s,v.observable A B s*nativeSteps v n (v.observable A B) s ∂v.stationary at hNative
  rw [hNative] at hgt
  exact ⟨β,t,hβ,ht,ht1,hg,hm,hv,(lt_div_iff₀ hv).mpr hgt⟩


/-- Native stochastic-integral form of the ALL-counts persistence estimate. -/
theorem native_iteration_interval (β : ℝ) (hc : coefficient β ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < δ →
      let v := (data β t).evenized
      let f := v.observable (SU2SevenLinkSpatialSeparation.oddA β) (SU2SevenLinkSpatialSeparation.oddB β)
      (∀ (g : Fin 6 → QuaternionSU2Representation.SU2) s,f (gaugeAction g s)=f s) ∧
      (∫ s,f s ∂v.stationary)=0 ∧ 0 < (∫ s,(f s)^2 ∂v.stationary) ∧
      ∀ n : ℕ, 1-(n:ℝ)*(1-coefficient β^4) ≤
        (∫ s,f s*nativeSteps v n f s ∂v.stationary)/(∫ s,(f s)^2 ∂v.stationary) ∧
        (∫ s,f s*nativeSteps v n f s ∂v.stationary)/(∫ s,(f s)^2 ∂v.stationary) ≤ 1 := by
  obtain ⟨δ,hδ,hδ1,hall⟩ := realized_iteration_interval β hc
  refine ⟨δ,hδ,hδ1,?_⟩
  intro t ht htδ
  let v := (data β t).evenized
  let A := SU2SevenLinkSpatialSeparation.oddA β
  let B := SU2SevenLinkSpatialSeparation.oddB β
  have he := hall t ht htδ
  have hv := v.observable_square_pos A B
  refine ⟨he.1,v.observable_centered A B (data β t).evenized_even,hv,?_⟩
  intro n
  obtain ⟨hL,hU,hEq⟩ := he.2.2.2 n
  rw [hEq,probe_square] at hL hU
  exact ⟨(le_div_iff₀ hv).mpr hL,(div_le_one hv).mpr hU⟩

end OperatorDerivativeRewrite.Foundation.SU2SevenLinkIteration
