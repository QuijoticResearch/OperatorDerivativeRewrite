import Foundation.RootMarkItoIsometry

/-! Genuine finite-horizon coefficient uniqueness from the positive Ito isometry. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
namespace OperatorDerivativeRewrite.Foundation.RootMarkIntegralUniqueness
open RootMarkStochasticIntegral RootMarkConditionalEnergy RootMarkItoIsometry
open MarkedRootRenewalProcess (MarkSample marks)
open RootRenewalWalkMarginal (initialSegment)

theorem totalIntegral_sub (a : ℝ) (H K : Fin 3 → Coefficients) (N : ℕ) :
    totalIntegral a (H-K) N = totalIntegral a H N-totalIntegral a K N := by
  funext η
  simp only [totalIntegral, stochasticIntegral, increment, Pi.add_apply, Pi.sub_apply,
    sub_mul, Finset.sum_sub_distrib]
  ring

theorem energy_nonneg (a : ℝ) (H : Fin 3 → Coefficients) (n : ℕ) (η : MarkSample) :
    0 ≤ energy a H n η := by
  unfold energy
  exact Finset.sum_nonneg fun r _ => mul_nonneg (sq_nonneg _) (pow_nonneg (by positivity) _)

theorem zero_energy (a : ℝ) (H : Fin 3 → Coefficients) (N : ℕ)
    (hH : totalIntegral a H N =ᵐ[marks] (0 : MarkSample → ℂ)) (j : ℕ) (hj : j < N) :
    energy a H j =ᵐ[marks] (0 : MarkSample → ℝ) := by
  have hL : (∫ η, ‖totalIntegral a H N η‖^2 ∂marks) = 0 := by
    calc
      _ = ∫ _ : MarkSample, (0 : ℝ) ∂marks := by
        apply integral_congr_ae
        filter_upwards [hH] with η hη
        simp [hη]
      _ = 0 := by simp
  have hsum : (∑ k ∈ Finset.range N, ∫ η, energy a H k η ∂marks) = 0 :=
    (ito_isometry a H N).symm.trans hL
  have hle : (∫ η, energy a H j η ∂marks) ≤ 0 := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, ∫ η, energy a H k η ∂marks :=
        Finset.single_le_sum (fun k _ => integral_nonneg (energy_nonneg a H k)) (Finset.mem_range.mpr hj)
      _ = 0 := hsum
  exact (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall (energy_nonneg a H j))
    (energy_integrable a H j)).mp (le_antisymm hle (integral_nonneg (energy_nonneg a H j)))

theorem zero_coefficients (a : ℝ) (ha : a ≠ 0) (H : Fin 3 → Coefficients) (N : ℕ)
    (hH : totalIntegral a H N =ᵐ[marks] (0 : MarkSample → ℂ)) (j : ℕ) (hj : j < N) (r : Fin 3) :
    (fun η => H r j (initialSegment j η)) =ᵐ[marks] (0 : MarkSample → ℂ) := by
  filter_upwards [zero_energy a H N hH j hj] with η hη
  change energy a H j η = 0 at hη
  have ht : ‖H r j (initialSegment j η)‖^2*(2*a^2)^(r.val+1) ≤ energy a H j η :=
    by
      change _ ≤ ∑ s : Fin 3, ‖H s j (initialSegment j η)‖^2*(2*a^2)^(s.val+1)
      exact Finset.single_le_sum
        (fun s _ => mul_nonneg (sq_nonneg ‖H s j (initialSegment j η)‖)
          (pow_nonneg (by positivity : 0 ≤ 2*a^2) (s.val+1))) (Finset.mem_univ r)
  rw [hη] at ht
  have hn : ‖H r j (initialSegment j η)‖^2 ≤ 0 :=
    le_of_mul_le_mul_right (by simpa using ht) (ComplexRootChannelGram.weight_pos a ha r)
  have hz : ‖H r j (initialSegment j η)‖ = 0 := by
    nlinarith [norm_nonneg (H r j (initialSegment j η))]
  exact norm_eq_zero.mp hz

theorem coefficients_unique (a : ℝ) (ha : a ≠ 0) (H K : Fin 3 → Coefficients) (N : ℕ)
    (hHK : totalIntegral a H N =ᵐ[marks] totalIntegral a K N) (j : ℕ) (hj : j < N) (r : Fin 3) :
    (fun η => H r j (initialSegment j η)) =ᵐ[marks] fun η => K r j (initialSegment j η) := by
  have he : totalIntegral a (H-K) N =ᵐ[marks] (0 : MarkSample → ℂ) := by
    rw [totalIntegral_sub]
    filter_upwards [hHK] with η hη
    simp only [Pi.sub_apply, Pi.zero_apply]
    rw [hη, sub_self]
  filter_upwards [zero_coefficients a ha (H-K) N he j hj r] with η hη
  change H r j (initialSegment j η)-K r j (initialSegment j η) = 0 at hη
  exact sub_eq_zero.mp hη

theorem finite_clark_unique (a : ℝ) (ha : a ≠ 0) (N : ℕ)
    (f : ComplexFourthRootWalk.Sample N → ℂ) :
    ∃ H : Fin 3 → Coefficients,
      ((fun η => f (initialSegment N η)-(∫ ξ, f (initialSegment N ξ) ∂marks)) =ᵐ[marks]
        totalIntegral a H N) ∧
      ∀ K : Fin 3 → Coefficients,
        ((fun η => f (initialSegment N η)-(∫ ξ, f (initialSegment N ξ) ∂marks)) =ᵐ[marks]
          totalIntegral a K N) →
        ∀ j : ℕ, j < N → ∀ r : Fin 3,
          (fun η => H r j (initialSegment j η)) =ᵐ[marks] fun η => K r j (initialSegment j η) := by
  obtain ⟨H,hH⟩ := RootMarkFiniteClark.finite_clark a ha N f
  have he : (fun η => stochasticIntegral a 0 (H 0) N η+
      stochasticIntegral a 1 (H 1) N η+stochasticIntegral a 2 (H 2) N η) =
      totalIntegral a H N := rfl
  rw [he] at hH
  refine ⟨H,hH,?_⟩
  intro K hK j hj r
  exact coefficients_unique a ha H K N (hH.symm.trans hK) j hj r

end OperatorDerivativeRewrite.Foundation.RootMarkIntegralUniqueness
