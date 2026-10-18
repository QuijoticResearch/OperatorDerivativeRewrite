import Foundation.PureOrderPolynomialConditioning

/-! Exact finite-grid predictable polynomial innovations with every power retained. -/
noncomputable section
open MeasureTheory
open scoped NNReal
namespace OperatorDerivativeRewrite.Foundation.PureOrderPolynomialInnovations
open PureOrderPolynomialConditioning PseudoPolynomialStein HigherHeatMultivariateMoments
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
open Classical in
theorem keep_insert (S : Finset ι) (i : ι) (hi : i ∉ S) (d : ι →₀ ℕ) :
    keep (insert i S) d = keep S d + Finsupp.single i (d i) := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp [keep_apply, hi]
  · by_cases hS : j ∈ S <;> simp [keep_apply, hj, hS]

open Classical in
theorem factor_insert (p : ℕ) (a : ι → ℝ) (S : Finset ι) (i : ι)
    (hi : i ∉ S) (d : ι →₀ ℕ) :
    factor p a S d = factor p a (insert i S) d * moment p (a i) (d i) := by
  classical
  calc
    _ = ∏ j, (if j ∈ insert i S then 1 else moment p (a j) (d j)) *
        (if j = i then moment p (a i) (d i) else 1) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j; simp [hi]
      · by_cases hS : j ∈ S <;> simp [hj, hS]
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [factor]

def innovation (p : ℕ) (a : ι → ℝ) (i : ι) (r : ℕ) : MvPolynomial ι ℝ :=
  MvPolynomial.X i ^ r - MvPolynomial.C (moment p (a i) r)

omit [Fintype ι] in
theorem innovation_zero (p : ℕ) (a : ι → ℝ) (i : ι) : innovation p a i 0 = 0 := by
  simp [innovation, moment_zero]

open Classical in
def coefficient (p : ℕ) (a : ι → ℝ) (S : Finset ι) (i : ι)
    (P : MvPolynomial ι ℝ) (d : ι →₀ ℕ) : MvPolynomial ι ℝ :=
  MvPolynomial.monomial (keep S d) (P.coeff d * factor p a (insert i S) d)

theorem coefficient_dependsOn (p : ℕ) (a : ι → ℝ) (S : Finset ι) (i : ι)
    (P : MvPolynomial ι ℝ) (d : ι →₀ ℕ) : dependsOn S (coefficient p a S i P d) :=
  kept_monomial_depends _ _ _

open Classical in
theorem monomial_innovation (p : ℕ) (a : ι → ℝ) (S : Finset ι) (i : ι)
    (hi : i ∉ S) (d : ι →₀ ℕ) (c : ℝ) :
    conditioning p a (insert i S) (MvPolynomial.monomial d c) -
        conditioning p a S (MvPolynomial.monomial d c) =
      MvPolynomial.monomial (keep S d) (c * factor p a (insert i S) d) *
        innovation p a i (d i) := by
  rw [conditioning_monomial, conditioning_monomial, keep_insert S i hi,
    factor_insert p a S i hi]
  have hc (v : ℝ) : (MvPolynomial.C v : MvPolynomial ι ℝ) = MvPolynomial.monomial 0 v := rfl
  simp only [innovation, mul_sub, MvPolynomial.X_pow_eq_monomial, hc,
    MvPolynomial.monomial_mul_monomial, mul_one, add_zero, mul_assoc]

open Classical in
theorem one_step_expansion (p : ℕ) (a : ι → ℝ) (S : Finset ι) (i : ι)
    (hi : i ∉ S) (P : MvPolynomial ι ℝ) :
    conditioning p a (insert i S) P - conditioning p a S P =
      ∑ d ∈ P.support, coefficient p a S i P d * innovation p a i (d i) := by
  classical
  calc
    _ = conditioning p a (insert i S)
        (∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)) -
        conditioning p a S (∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d)) :=
      congrArg (fun Q => conditioning p a (insert i S) Q - conditioning p a S Q)
        (MvPolynomial.as_sum P)
    _ = _ := by
      rw [map_sum, map_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro d _
      exact monomial_innovation p a S i hi d (P.coeff d)


theorem one_step_next (p : ℕ) (a : ι → ℝ) (S T : Finset ι) (i : ι)
    (hi : i ∉ S) (hT : ∀ j, j ∈ T ↔ j = i ∨ j ∈ S) (P : MvPolynomial ι ℝ) :
    conditioning p a T P - conditioning p a S P =
      ∑ d ∈ P.support, coefficient p a S i P d * innovation p a i (d i) := by
  classical
  have hs : T = insert i S := by
    ext j
    simpa only [Finset.mem_insert] using hT j
  rw [hs]
  exact one_step_expansion p a S i hi P

open Classical in
theorem conditioned_increment_zero (p : ℕ) (a : ι → ℝ) (S : Finset ι) (i : ι)
    (P : MvPolynomial ι ℝ) :
    conditioning p a S (conditioning p a (insert i S) P - conditioning p a S P) = 0 := by
  classical
  rw [map_sub, conditioning_tower, conditioning_idempotent]
  rw [Finset.inter_eq_left.mpr (Finset.subset_insert i S), sub_self]

open Classical in
theorem actual_innovation_pairing_zero (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (i : ι) (P Q : MvPolynomial ι ℝ)
    (hQ : supported S Q) :
    (∫ᵛ x, value (conditioning (2*m) (parameters m t) (insert i S) P -
      conditioning (2*m) (parameters m t) S P) x * value Q x
      ∂<•HigherHeatSignedLaws.incrementLaw m hm t ht) = 0 := by
  have he := actual_past_polynomial_pairing m hm t ht S
    (conditioning (2*m) (parameters m t) (insert i S) P -
      conditioning (2*m) (parameters m t) S P) Q hQ
  rw [conditioned_increment_zero] at he
  simpa [value] using he.symm

def initialSegment (N k : ℕ) : Finset (Fin N) := Finset.univ.filter (fun i => i.val < k)

theorem initialSegment_zero (N : ℕ) : initialSegment N 0 = ∅ := by
  simp [initialSegment]

theorem initialSegment_full (N : ℕ) : initialSegment N N = Finset.univ := by
  ext i
  simp [initialSegment]

theorem new_cell_not_mem {N : ℕ} (i : Fin N) : i ∉ initialSegment N i.val := by
  simp [initialSegment]

theorem initialSegment_succ {N : ℕ} (i : Fin N) :
    initialSegment N (i.val+1) = insert i (initialSegment N i.val) := by
  ext j
  simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Fin.ext_iff]
  omega

omit [Fintype ι] in
theorem telescope (F : ℕ → MvPolynomial ι ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (F (k+1) - F k)) = F N - F 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ, ih]; abel

theorem chronological_decomposition (N p : ℕ) (a : Fin N → ℝ)
    (P : MvPolynomial (Fin N) ℝ) :
    P - conditioning p a ∅ P = ∑ i : Fin N,
      (conditioning p a (initialSegment N (i.val+1)) P -
        conditioning p a (initialSegment N i.val) P) := by
  have he := Fin.sum_univ_eq_sum_range (fun k =>
    conditioning p a (initialSegment N (k+1)) P - conditioning p a (initialSegment N k) P) N
  rw [he]
  have ht := telescope (fun k => conditioning p a (initialSegment N k) P) N
  simpa only [initialSegment_full, initialSegment_zero, conditioning_univ] using ht.symm

theorem full_jet_reconstruction (N p : ℕ) (a : Fin N → ℝ)
    (P : MvPolynomial (Fin N) ℝ) :
    P - conditioning p a ∅ P = ∑ i : Fin N, ∑ d ∈ P.support,
      coefficient p a (initialSegment N i.val) i P d * innovation p a i (d i) := by
  have hcell (i : Fin N) :
      conditioning p a (initialSegment N (i.val+1)) P -
          conditioning p a (initialSegment N i.val) P =
        ∑ d ∈ P.support, coefficient p a (initialSegment N i.val) i P d *
          innovation p a i (d i) := by
    apply one_step_next p a (initialSegment N i.val) (initialSegment N (i.val+1)) i
      (new_cell_not_mem i) _ P
    intro j
    simp only [initialSegment, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
    omega
  have hf : (fun i : Fin N =>
      conditioning p a (initialSegment N (i.val+1)) P -
        conditioning p a (initialSegment N i.val) P) =
      (fun i : Fin N => ∑ d ∈ P.support,
        coefficient p a (initialSegment N i.val) i P d * innovation p a i (d i)) := funext hcell
  have he := congrArg (fun f : Fin N → MvPolynomial (Fin N) ℝ => ∑ i, f i) hf
  exact (chronological_decomposition N p a P).trans he


omit [Fintype ι] in
theorem value_sum {α : Type*} (A : Finset α) (F : α → MvPolynomial ι ℝ) (x : ι → ℝ) :
    value (∑ j ∈ A, F j) x = ∑ j ∈ A, value (F j) x := by simp [value]

theorem actual_full_jet_reconstruction (N m : ℕ) (hm : 0 < m)
    (t : Fin N → ℝ≥0) (ht : ∀ i, 0 < t i) (P : MvPolynomial (Fin N) ℝ)
    (x : Fin N → ℝ) :
    value P x - mean m hm t ht P = ∑ i : Fin N, ∑ d ∈ P.support,
      value (coefficient (2*m) (parameters m t) (initialSegment N i.val) i P d) x *
        value (innovation (2*m) (parameters m t) i (d i)) x := by
  have he := congrArg (fun Q => value Q x) (full_jet_reconstruction N (2*m) (parameters m t) P)
  rw [value_sub, actual_value_empty m hm t ht P x] at he
  simpa only [value_sum, value_mul] using he



theorem actual_innovation_mean (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (i : ι) (r : ℕ) :
    mean m hm t ht (innovation (2*m) (parameters m t) i r) = 0 := by
  classical
  have hp : (∏ j, moment (2*m) (parameters m t j) ((Finsupp.single i r) j)) =
      moment (2*m) (parameters m t i) r := by
    calc
      _ = ∏ j, if j = i then moment (2*m) (parameters m t i) r else 1 := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases hj : j = i
        · subst j; simp
        · simp [hj, moment_zero]
      _ = _ := by simp
  rw [innovation, map_sub, MvPolynomial.X_pow_eq_monomial, actual_mean_monomial,
    mean_C, hp, one_mul, sub_self]

theorem actual_term_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ i, 0 < t i) (S : Finset ι) (i : ι) (P : MvPolynomial ι ℝ) (d : ι →₀ ℕ) :
    (HigherHeatSignedLaws.incrementLaw m hm t ht).Integrable (fun x =>
      value (coefficient (2*m) (parameters m t) S i P d) x *
        value (innovation (2*m) (parameters m t) i (d i)) x) := by
  have he : (fun x => value (coefficient (2*m) (parameters m t) S i P d) x *
      value (innovation (2*m) (parameters m t) i (d i)) x) =
      value (coefficient (2*m) (parameters m t) S i P d *
        innovation (2*m) (parameters m t) i (d i)) := by
    funext x
    rw [value_mul]
  rw [he]
  exact polynomial_integrable m hm t ht _


end OperatorDerivativeRewrite.Foundation.PureOrderPolynomialInnovations
