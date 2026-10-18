import Foundation.HigherHeatDyadicConditioning

/-! Signed causal endomorphisms on the common polynomial-cylinder domain. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCylindricalConditioning
open HigherHeatPolynomialCylinders HigherHeatDyadicConditioning PureOrderPolynomialConditioning

theorem transfer_trans (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) (P : Test i) :
    transfer j k hjk (transfer i j hij P) = transfer i k (hij.trans hjk) P :=
  (Nat.leRecOn_trans hij hjk P).symm

def commonComponent (b : ℕ) (g : ∀ n, b ≤ n → Test n →ₗ[ℝ] Cylinder) (i : ℕ) :
    Test i →ₗ[ℝ] Cylinder :=
  (g (max i b) (Nat.le_max_right i b)).comp
    (transition i (max i b) (Nat.le_max_left i b)).toLinearMap

theorem commonComponent_compatible (b : ℕ) (g : ∀ n, b ≤ n → Test n →ₗ[ℝ] Cylinder)
    (hg : ∀ i j (hi : b ≤ i) (hij : i ≤ j) (P : Test i),
      g j (hi.trans hij) (transfer i j hij P) = g i hi P)
    (i j : ℕ) (hij : i ≤ j) (P : Test i) :
    commonComponent b g j (transfer i j hij P) = commonComponent b g i P := by
  have hmax : max i b ≤ max j b := max_le_max hij le_rfl
  change g (max j b) _ (transfer j (max j b) _ (transfer i j hij P)) =
    g (max i b) _ (transfer i (max i b) _ P)
  rw [transfer_trans i j (max j b) hij (Nat.le_max_left j b) P]
  have he := hg (max i b) (max j b) (Nat.le_max_right i b) hmax
    (transfer i (max i b) (Nat.le_max_left i b) P)
  rw [transfer_trans i (max i b) (max j b) (Nat.le_max_left i b) hmax P] at he
  exact he

def cofinalLift (b : ℕ) (g : ∀ n, b ≤ n → Test n →ₗ[ℝ] Cylinder)
    (hg : ∀ i j (hi : b ≤ i) (hij : i ≤ j) (P : Test i),
      g j (hi.trans hij) (transfer i j hij P) = g i hi P) : Cylinder →ₗ[ℝ] Cylinder :=
  DirectLimit.Module.lift ℝ ℕ Test transition (commonComponent b g)
    (commonComponent_compatible b g hg)

theorem cofinalLift_apply (b : ℕ) (g : ∀ n, b ≤ n → Test n →ₗ[ℝ] Cylinder)
    (hg : ∀ i j (hi : b ≤ i) (hij : i ≤ j) (P : Test i),
      g j (hi.trans hij) (transfer i j hij P) = g i hi P)
    (n : ℕ) (hn : b ≤ n) (P : Test n) :
    cofinalLift b g hg (cylinderOf n P) = g n hn P := by
  change g (max n b) _ (transfer n (max n b) _ P) = _
  have he (k : ℕ) (hk : k = n) (hnk : n ≤ k) (hbk : b ≤ k) :
      g k hbk (transfer n k hnk P) = g n hn P := by
    subst k
    rw [transfer_self]
  exact he (max n b) (max_eq_left hn) _ _

theorem tail_induction (b : ℕ) (p : Cylinder → Prop)
    (h : ∀ n, b ≤ n → ∀ P : Test n, p (cylinderOf n P)) (F : Cylinder) : p F := by
  induction F using DirectLimit.induction with
  | _ n P =>
    change p (cylinderOf n P)
    rw [← cylinder_refinement n (max n b) (Nat.le_max_left n b) P]
    exact h (max n b) (Nat.le_max_right n b) _

def tailComponent (m : ℕ) (T : ℝ≥0) (b : ℕ) (S : Finset (Fin (size b)))
    (n : ℕ) (hn : b ≤ n) : Test n →ₗ[ℝ] Cylinder :=
  (cylinderOf n).toLinearMap.comp (localProjection m T n (cells b S n hn))

theorem tailComponent_compatible (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (i j : ℕ) (hi : b ≤ i) (hij : i ≤ j) (P : Test i) :
    tailComponent m T b S j (hi.trans hij) (transfer i j hij P) =
      tailComponent m T b S i hi P := by
  change cylinderOf j (localProjection m T j _ (transfer i j hij P)) =
    cylinderOf i (localProjection m T i _ P)
  rw [localProjection_transfer m hm T hT b S i j hi hij P,
    cylinder_refinement i j hij (localProjection m T i (cells b S i hi) P)]

def projection (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) : Cylinder →ₗ[ℝ] Cylinder :=
  cofinalLift b (tailComponent m T b S) (tailComponent_compatible m hm T hT b S)

theorem projection_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (n : ℕ) (hn : b ≤ n) (P : Test n) :
    projection m hm T hT b S (cylinderOf n P) =
      cylinderOf n (localProjection m T n (cells b S n hn) P) :=
  cofinalLift_apply b _ _ n hn P

theorem projection_idempotent (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (F : Cylinder) :
    projection m hm T hT b S (projection m hm T hT b S F) = projection m hm T hT b S F := by
  apply tail_induction b (fun F =>
    projection m hm T hT b S (projection m hm T hT b S F) = projection m hm T hT b S F) _ F
  intro n hn P
  rw [projection_apply m hm T hT b S n hn P,
    projection_apply m hm T hT b S n hn (localProjection m T n (cells b S n hn) P),
    localProjection_idempotent]

open Classical in
theorem projection_tower (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S U : Finset (Fin (size b))) (F : Cylinder) :
    projection m hm T hT b S (projection m hm T hT b U F) =
      projection m hm T hT b (S ∩ U) F := by
  classical
  apply tail_induction b (fun F =>
    projection m hm T hT b S (projection m hm T hT b U F) =
      projection m hm T hT b (S ∩ U) F) _ F
  intro n hn P
  rw [projection_apply m hm T hT b U n hn P,
    projection_apply m hm T hT b S n hn (localProjection m T n (cells b U n hn) P),
    projection_apply m hm T hT b (S ∩ U) n hn P,
    localProjection_tower, cells_inter]

theorem projection_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (F : Cylinder) :
    cylindricalExpectation m hm T hT (projection m hm T hT b S F) =
      cylindricalExpectation m hm T hT F := by
  apply tail_induction b (fun F => cylindricalExpectation m hm T hT (projection m hm T hT b S F) =
    cylindricalExpectation m hm T hT F) _ F
  intro n hn P
  rw [projection_apply m hm T hT b S n hn P, cylindricalExpectation_apply,
    cylindricalExpectation_apply, localProjection_expectation]


theorem projection_commute (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S U : Finset (Fin (size b))) (F : Cylinder) :
    projection m hm T hT b S (projection m hm T hT b U F) =
      projection m hm T hT b U (projection m hm T hT b S F) := by
  classical
  rw [projection_tower, projection_tower, Finset.inter_comm]

theorem projection_C (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (c : ℝ) :
    projection m hm T hT b S (algebraMap ℝ Cylinder c) = algebraMap ℝ Cylinder c := by
  have hc : algebraMap ℝ Cylinder c = cylinderOf b (MvPolynomial.C c) :=
    (MvPolynomial.algHom_C (cylinderOf b) c).symm
  rw [hc, projection_apply m hm T hT b S b le_rfl (MvPolynomial.C c), localProjection_C]

def dyadicProjection (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T) (b q : ℕ) :
    Cylinder →ₗ[ℝ] Cylinder := projection m hm T hT b (initialPast b q)

theorem dyadicProjection_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b q n : ℕ) (hn : b ≤ n) (P : Test n) :
    dyadicProjection m hm T hT b q (cylinderOf n P) =
      cylinderOf n (localProjection m T n (initialPast n (q*2^(n-b))) P) := by
  rw [dyadicProjection, projection_apply m hm T hT b (initialPast b q) n hn P,
    cells_initialPast]

def pathProjection (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) :
    HigherHeatPolynomialPathDomain.realizedAlgebra →ₗ[ℝ]
      HigherHeatPolynomialPathDomain.realizedAlgebra :=
  HigherHeatPolynomialPathDomain.realizationEquiv.toLinearMap.comp
    ((projection m hm T hT b S).comp
      HigherHeatPolynomialPathDomain.realizationEquiv.symm.toLinearMap)

theorem pathProjection_apply (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (F : Cylinder) :
    pathProjection m hm T hT b S (HigherHeatPolynomialPathDomain.realizationEquiv F) =
      HigherHeatPolynomialPathDomain.realizationEquiv (projection m hm T hT b S F) := by
  simp [pathProjection]

theorem pathProjection_expectation (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b)))
    (F : HigherHeatPolynomialPathDomain.realizedAlgebra) :
    HigherHeatPolynomialPathDomain.pathExpectation m hm T hT (pathProjection m hm T hT b S F) =
      HigherHeatPolynomialPathDomain.pathExpectation m hm T hT F := by
  obtain ⟨G, rfl⟩ := HigherHeatPolynomialPathDomain.realizationEquiv.surjective F
  rw [pathProjection_apply, HigherHeatPolynomialPathDomain.pathExpectation_apply,
    HigherHeatPolynomialPathDomain.pathExpectation_apply, projection_expectation]



theorem projection_base_refinement (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (F : Cylinder) :
    projection m hm T hT b S F = projection m hm T hT (b+1)
      (HigherHeatConditionalRefinement.pastCells (@HigherHeatGridDoubling.pairBlock (size b)) S) F := by
  apply tail_induction (b+1) (fun F => projection m hm T hT b S F =
    projection m hm T hT (b+1)
      (HigherHeatConditionalRefinement.pastCells (@HigherHeatGridDoubling.pairBlock (size b)) S) F) _ F
  intro n hn P
  calc
    _ = cylinderOf n (localProjection m T n (cells b S n ((Nat.le_succ b).trans hn)) P) :=
      projection_apply m hm T hT b S n ((Nat.le_succ b).trans hn) P
    _ = cylinderOf n (localProjection m T n
        (cells (b+1)
          (HigherHeatConditionalRefinement.pastCells (@HigherHeatGridDoubling.pairBlock (size b)) S) n hn) P) :=
      congrArg (fun A : Finset (Fin (size n)) => cylinderOf n (localProjection m T n A P))
        (cells_refine_base b S n hn)
    _ = _ := (projection_apply m hm T hT (b+1)
      (HigherHeatConditionalRefinement.pastCells (@HigherHeatGridDoubling.pairBlock (size b)) S) n hn P).symm

theorem dyadicProjection_refinement (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b q : ℕ) (F : Cylinder) :
    dyadicProjection m hm T hT b q F = dyadicProjection m hm T hT (b+1) (2*q) F := by
  calc
    _ = projection m hm T hT (b+1)
        (HigherHeatConditionalRefinement.pastCells (@HigherHeatGridDoubling.pairBlock (size b))
          (initialPast b q)) F := projection_base_refinement m hm T hT b (initialPast b q) F
    _ = _ := congrArg (fun A : Finset (Fin (size (b+1))) => projection m hm T hT (b+1) A F)
      (pastCells_initialPast b q)



theorem dyadicProjection_tower (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b q r : ℕ) (F : Cylinder) :
    dyadicProjection m hm T hT b q (dyadicProjection m hm T hT b r F) =
      dyadicProjection m hm T hT b (min q r) F := by
  classical
  have hs : initialPast b q ∩ initialPast b r = initialPast b (min q r) := by
    ext j
    simp only [initialPast, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  change projection m hm T hT b (initialPast b q)
    (projection m hm T hT b (initialPast b r) F) = projection m hm T hT b (initialPast b (min q r)) F
  rw [projection_tower, hs]

theorem dyadicProjection_fixed (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b q n : ℕ) (hn : b ≤ n) (P : Test n)
    (hP : supported (initialPast n (q*2^(n-b))) P) :
    dyadicProjection m hm T hT b q (cylinderOf n P) = cylinderOf n P := by
  rw [dyadicProjection_apply m hm T hT b q n hn P]
  have he := conditioning_fixed_of_supported (2*m)
    (parameters m (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n))
    (initialPast n (q*2^(n-b))) P hP
  exact congrArg (fun Q => cylinderOf n Q) he

theorem projection_past_pairing (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b))) (n : ℕ) (hn : b ≤ n) (P Q : Test n)
    (hQ : supported (cells b S n hn) Q) :
    cylindricalExpectation m hm T hT
      (projection m hm T hT b S (cylinderOf n P) * cylinderOf n Q) =
      cylindricalExpectation m hm T hT (cylinderOf n P * cylinderOf n Q) := by
  rw [projection_apply m hm T hT b S n hn P,
    ← map_mul (cylinderOf n), ← map_mul (cylinderOf n),
    cylindricalExpectation_apply, cylindricalExpectation_apply]
  change (∫ᵛ x, HigherHeatMultivariateMoments.value (localProjection m T n (cells b S n hn) P * Q) x
      ∂<•HigherHeatSignedLaws.incrementLaw m hm
        (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
        (fun _ => HigherHeatDyadicLaws.duration_pos T hT n)) =
    (∫ᵛ x, HigherHeatMultivariateMoments.value (P*Q) x
      ∂<•HigherHeatSignedLaws.incrementLaw m hm
        (fun _ : Fin (size n) => HigherHeatDyadicLaws.duration T n)
        (fun _ => HigherHeatDyadicLaws.duration_pos T hT n))
  simp_rw [HigherHeatMultivariateMoments.value_mul]
  exact actual_past_polynomial_pairing m hm _ _ (cells b S n hn) P Q hQ

theorem pathProjection_idempotent (m : ℕ) (hm : 0 < m) (T : ℝ≥0) (hT : 0 < T)
    (b : ℕ) (S : Finset (Fin (size b)))
    (F : HigherHeatPolynomialPathDomain.realizedAlgebra) :
    pathProjection m hm T hT b S (pathProjection m hm T hT b S F) = pathProjection m hm T hT b S F := by
  obtain ⟨G, rfl⟩ := HigherHeatPolynomialPathDomain.realizationEquiv.surjective F
  rw [pathProjection_apply, pathProjection_apply, projection_idempotent]


end OperatorDerivativeRewrite.Foundation.HigherHeatCylindricalConditioning
