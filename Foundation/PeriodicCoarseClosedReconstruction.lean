import Foundation.PeriodicCoarseCurlCoordinates

/-! Constructive reconstruction of every closed coarse field by a gradient and a harmonic field. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCoarseClosedReconstruction
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseGaugeDiagnostics PeriodicPathHarmonic PeriodicCoarseWalshBasis
open PeriodicCoarseCurlCoordinates
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def pivot (T : Finset Direction) : Direction := if h : T.Nonempty then T.min' h else 0

theorem pivot_mem (T : Finset Direction) (h : T.Nonempty) : pivot T ∈ T := by
  simp only [pivot, dif_pos h]
  exact Finset.min'_mem _ _

def potential (f : Field) : CoarseVertex → ℝ :=
  ∑ T : Finset Direction, ((-1/2 : ℝ) * coefficient (T,pivot T) f) • character T

def harmonicVector (f : Field) (i : Direction) : ℝ := coefficient (∅,i) f

theorem mode_apply (a : Label) (e : CoarseEdge) :
    mode a e = if e.2 = a.2 then character a.1 e.1 else 0 := by
  by_cases h : e.2 = a.2 <;> simp [mode, modeZ, character, h]

theorem harmonic_reconstruction (a : Direction → ℝ) :
    harmonicField a = ∑ i : Direction, a i • mode (∅,i) := by
  funext e
  simp [harmonicField_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mode_apply,
    character, characterZ, mul_ite, eq_comm]

theorem harmonicVector_mean (f : Field) (i : Direction) :
    harmonicVector f i = (1/16 : ℝ) * ∑ q : CoarseVertex, f (q,i) := by
  have hm : dotProduct f (mode (∅,i)) = ∑ q : CoarseVertex, f (q,i) := by
    unfold dotProduct
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro q _
    simp [mode_apply, character, characterZ, mul_ite, eq_comm]
  have h := coefficient_dot (∅,i) f
  rw [hm] at h
  change (∑ q : CoarseVertex, f (q,i)) = 16 * harmonicVector f i at h
  linarith

theorem harmonic_coefficient (f : Field) (a : Label) :
    coefficient a (harmonicField (harmonicVector f)) =
      if a.1 = ∅ then coefficient a f else 0 := by
  rw [harmonic_reconstruction]
  simp only [map_sum, map_smul, coefficient_mode, smul_eq_mul]
  rcases a with ⟨T,i⟩
  by_cases h : T = ∅
  · subst T
    simp [harmonicVector]
  · simp [Prod.mk.injEq, h, Ne.symm h]

theorem gradient_potential (f : Field) :
    coarseGradient (potential f) = ∑ T : Finset Direction,
      coefficient (T,pivot T) f • ∑ i ∈ T, mode (T,i) := by
  rw [potential, map_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [map_smul, gradient_character, smul_smul]
  congr 1
  ring

theorem coefficient_mode_sum (T S : Finset Direction) (k : Direction) :
    coefficient (S,k) (∑ i ∈ T, mode (T,i)) = if T = S ∧ k ∈ T then 1 else 0 := by
  simp only [map_sum, coefficient_mode]
  by_cases h : T = S
  · subst S
    simp
  · simp [Prod.mk.injEq, h]

theorem potential_gradient_coefficient (f : Field) (a : Label) :
    coefficient a (coarseGradient (potential f)) =
      if a.2 ∈ a.1 then coefficient (a.1,pivot a.1) f else 0 := by
  rcases a with ⟨S,k⟩
  rw [gradient_potential]
  simp only [map_sum, map_smul, smul_eq_mul, coefficient_mode]
  simp [Prod.mk.injEq, ite_and, mul_ite]

theorem closed_reconstruction (f : Field) (hf : coarseIncidence f = 0) :
    f = coarseGradient (potential f) + harmonicField (harmonicVector f) := by
  apply basis.repr.injective
  ext a
  change coefficient a f = coefficient a (coarseGradient (potential f) +
    harmonicField (harmonicVector f))
  rw [map_add, potential_gradient_coefficient, harmonic_coefficient]
  by_cases h : a.1 = ∅
  · simp [h]
  · rw [if_neg h]
    have hn : a.1.Nonempty := Finset.nonempty_iff_ne_empty.mpr h
    rw [closed_coordinate f hf a.1 (pivot a.1) (pivot_mem a.1 hn) a.2]
    simp

theorem decomposition_class (φ : CoarseVertex → ℝ) (a : Direction → ℝ) :
    (Submodule.Quotient.mk (coarseGradient φ + harmonicField a) : CoarseGaugeQuotient) =
      harmonicClass a := by
  apply (Submodule.Quotient.eq _).mpr
  have h : coarseGradient φ + harmonicField a - harmonicField a = coarseGradient φ := by abel
  rw [h]
  exact ⟨φ, rfl⟩

theorem closed_class (f : Field) (hf : coarseIncidence f = 0) :
    (Submodule.Quotient.mk f : CoarseGaugeQuotient) = harmonicClass (harmonicVector f) := by
  conv_lhs => rw [closed_reconstruction f hf]
  exact decomposition_class _ _

theorem harmonic_unique (φ ψ : CoarseVertex → ℝ) (a b : Direction → ℝ)
    (h : coarseGradient φ + harmonicField a = coarseGradient ψ + harmonicField b) : a = b := by
  apply harmonicClass_injective
  rw [← decomposition_class φ a, h, decomposition_class ψ b]

end OperatorDerivativeRewrite.Foundation.PeriodicCoarseClosedReconstruction
