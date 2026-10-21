import Foundation.HigherHeatConditionalCellBound

/-! Actual conditional-cut estimates in the completed test dual, uniform
under refinement of each fixed multitime cylinder. -/
noncomputable section
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatConditionalCutBound
open HigherHeatPolynomialCylinders HigherHeatAnalyticCylinderDomain HigherHeatCompletedPairing
open HigherHeatPredictableJetBounds HigherHeatDyadicConditioning HigherHeatConditionalCellBound
open HigherHeatRefinedPredictableJets HigherHeatRefinementDegree

theorem conditional_cut_bound (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (D : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n (P : Test n), P.totalDegree ≤ D →
      ∀ a b : ℕ, a ≤ b → b ≤ size n →
      ‖pairing m hm T hT (core (cylinderOf n
        (localProjection m T n (initialPast n b) P-
          localProjection m T n (initialPast n a) P)))‖ ≤
        K*((b-a:ℕ):ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*‖core (cylinderOf n P)‖ := by
  obtain ⟨K, hK, hc⟩ := conditional_cell_bound m hm T hT D
  refine ⟨K, hK, ?_⟩
  intro n P hD a b hab hb
  rw [map_sub, map_sub, map_sub]
  let f : ℕ → HigherHeatPairedDualCausality.Dual := fun c =>
    pairing m hm T hT (core (cylinderOf n (localProjection m T n (initialPast n c) P)))
  change ‖f b-f a‖ ≤ _
  revert hb
  induction b, hab using Nat.le_induction with
  | base => intro hb; simp
  | succ b hab ih =>
    intro hb
    have hp := ih (by omega)
    have hs : ‖f (b+1)-f b‖ ≤
        K*(HigherHeatDyadicLaws.duration 1 n:ℝ)*‖core (cylinderOf n P)‖ := by
      simpa only [f, nextConditioned, map_sub] using hc n ⟨b, by omega⟩ P hD
    calc
      _ = ‖(f (b+1)-f b)+(f b-f a)‖ := by congr 1; abel
      _ ≤ ‖f (b+1)-f b‖+‖f b-f a‖ := norm_add_le _ _
      _ ≤ K*(HigherHeatDyadicLaws.duration 1 n:ℝ)*‖core (cylinderOf n P)‖+
          K*((b-a:ℕ):ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*‖core (cylinderOf n P)‖ :=
        add_le_add hs hp
      _ = _ := by rw [Nat.succ_sub hab, Nat.cast_succ]; ring

theorem refined_cut_bound (b : ℕ) (P : Test b) (m : ℕ) (hm : 0 < m)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n a c : ℕ, a ≤ c → c ≤ size n →
      ‖pairing m hm T hT (core (cylinderOf n
        (localProjection m T n (initialPast n c) (refinedInput b P n)-
          localProjection m T n (initialPast n a) (refinedInput b P n))))‖ ≤
        K*((c-a:ℕ):ℝ)*(HigherHeatDyadicLaws.duration 1 n:ℝ)*‖core (cylinderOf b P)‖ := by
  obtain ⟨K, hK, hc⟩ := conditional_cut_bound m hm T hT P.totalDegree
  refine ⟨K, hK, ?_⟩
  intro n a c hac hcn
  apply (hc n (refinedInput b P n) (refined_input_degree b P n) a c hac hcn).trans
  exact mul_le_mul_of_nonneg_left (refined_core_bound b P n) (by positivity)

end OperatorDerivativeRewrite.Foundation.HigherHeatConditionalCutBound
