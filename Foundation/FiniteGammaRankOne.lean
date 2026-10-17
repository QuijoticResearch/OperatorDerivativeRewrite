import Foundation.FiniteGammaTensor

/-! Single products do not form a dense subset of the completed finite Gamma module. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteGammaRankOne
open FiniteGammaSeed FiniteGammaTensor
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def target : Form := WithLp.toLp 2 (fun p =>
  if p = (State.o, 0) ∨ p = (State.x, 1) then 1 else 0)

theorem state_sum (f : State → ℝ) : ∑ s, f s = f State.o + f State.x + f State.y := by
  have hu : (Finset.univ : Finset State) = {State.o, State.x, State.y} := by decide
  rw [hu]
  simp [add_comm, add_left_comm]

theorem rank_one_gap_identity (a b c d : ℝ) :
    (a*c-1)^2 + (a*d)^2 + (b*c)^2 + (b*d-1)^2 =
      1 + (a*c+b*d-1)^2 + (a*d-b*c)^2 := by ring

theorem distance_squared_gap (f u : Algebra) : 1 ≤ ‖singleForm f u - target‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, state_sum]
  simp only [Fin.sum_univ_two, PiLp.sub_apply, singleForm_apply]
  change 1 ≤
    ((u State.o * beta f 0 - 1)^2 + (u State.o * beta f 1 - 0)^2) +
    ((u State.x * beta f 0 - 0)^2 + (u State.x * beta f 1 - 1)^2) +
    ((u State.y * beta f 0 - 0)^2 + (u State.y * beta f 1 - 0)^2)
  have h := rank_one_gap_identity (u State.o) (u State.x) (beta f 0) (beta f 1)
  nlinarith [sq_nonneg (u State.o * beta f 0 + u State.x * beta f 1 - 1),
    sq_nonneg (u State.o * beta f 1 - u State.x * beta f 0),
    sq_nonneg (u State.y * beta f 0), sq_nonneg (u State.y * beta f 1)]

/-- The exact probability normalization gives squared distance at least one third. -/
theorem probability_distance_gap (f u : Algebra) :
    (1/3 : ℝ) ≤ (1/3 : ℝ) * ‖singleForm f u - target‖^2 := by
  linarith [distance_squared_gap f u]

theorem single_products_not_dense :
    ¬ DenseRange (fun p : FiniteGammaSeed.Algebra × FiniteGammaSeed.Algebra =>
      singleForm p.1 p.2) := by
  intro hd
  obtain ⟨⟨f,u⟩, h⟩ := Metric.denseRange_iff.mp hd target (1/2) (by norm_num)
  rw [dist_eq_norm] at h
  rw [norm_sub_rev] at h
  have hg := distance_squared_gap f u
  have hn := norm_nonneg (singleForm f u - target)
  nlinarith

end OperatorDerivativeRewrite.Foundation.FiniteGammaRankOne
