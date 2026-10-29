import Foundation.FourCubeCompletedHaar
import Foundation.OneSidedPhysicalProjection

/-! Strict positivity of the NEW full32-link incidence Gram after the exact
negative-side diagonal completion. No31-link gauge pin or Haar limit is assumed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeCompletedGram
open OneSidedBlockIncidence OneSidedBlockKernel OneSidedBlockRank OneSidedGramSector
open OneSidedPinnedInterior FourCubeNegativeCompletion

attribute [local irreducible] edges innerFaces upperFaces

def weight (e : Interior) : ℝ := (multiplicity e : ℝ)
def penalty (f : Field) : ℝ := ∑ e : Interior,weight e*(f e)^2
def quadratic (f : Field) : ℝ := realEnergy (extend f)+penalty f
def gram : Matrix Interior Interior ℝ :=
  OneSidedPhysicalProjection.fullGram+Matrix.diagonal weight

theorem weight_nonneg (e : Interior) : 0 ≤ weight e := Nat.cast_nonneg _
theorem pole_weight : weight pole=3 := by norm_num [weight,pole_multiplicity]

theorem penalty_nonneg (f : Field) : 0 ≤ penalty f :=
  Finset.sum_nonneg (fun e _ => mul_nonneg (weight_nonneg e) (sq_nonneg (f e)))

theorem quadratic_nonneg (f : Field) : 0 ≤ quadratic f :=
  add_nonneg (realEnergy_nonneg _) (penalty_nonneg f)

/-- Exact full32-variable identity; the diagonal penalty removes the old gauge kernel. -/
theorem gram_energy (f : Field) : dotProduct f (gram.mulVec f)=quadratic f := by
  rw [gram,Matrix.add_mulVec,dotProduct_add,OneSidedPhysicalProjection.fullGram_eq_gram,
    OneSidedGramSector.gram_energy]
  unfold quadratic
  congr 1
  change (∑ e : Interior,f e*((Matrix.diagonal weight).mulVec f) e)=
    ∑ e : Interior,weight e*(f e)^2
  simp only [Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem quadratic_zero_iff (f : Field) : quadratic f=0 ↔ f=0 := by
  constructor
  · intro h
    change realEnergy (extend f)+penalty f=0 at h
    have he0 := realEnergy_nonneg (extend f)
    have hp0 := penalty_nonneg f
    have he : realEnergy (extend f)=0 := by linarith
    have hp : penalty f=0 := by linarith
    have hs := Finset.single_le_sum
      (fun e (_ : e∈Finset.univ) => mul_nonneg (weight_nonneg e) (sq_nonneg (f e)))
      (Finset.mem_univ pole)
    change weight pole*(f pole)^2 ≤ penalty f at hs
    rw [pole_weight,hp] at hs
    have hr : f pole=0 := sq_eq_zero_iff.mp (by nlinarith [sq_nonneg (f pole)])
    funext e
    have hh := kernel_classification (extend f) he e.val e.property
    have hfield := extend_on f e
    have hroot := extend_on f pole
    change extend f (origin,0)=f pole at hroot
    rw [hfield,hroot,hr,zero_mul] at hh
    exact hh
  · intro h
    rw [h,← gram_energy]
    simp

theorem quadratic_positive (f : Field) (hf : f≠0) : 0<quadratic f := by
  apply lt_of_le_of_ne (quadratic_nonneg f)
  intro he
  exact hf ((quadratic_zero_iff f).mp he.symm)

theorem gram_positive (f : Field) (hf : f≠0) : 0<dotProduct f (gram.mulVec f) := by
  rw [gram_energy]
  exact quadratic_positive f hf

theorem gram_hermitian : gram.IsHermitian := by
  classical
  have hg : OneSidedPhysicalProjection.fullGram.IsHermitian := by
    simpa only [OneSidedPhysicalProjection.fullGram,Matrix.conjTranspose_eq_transpose_of_trivial]
      using Matrix.isHermitian_conjTranspose_mul_self OneSidedPhysicalProjection.fullMatrix
  have hd : (Matrix.diagonal weight).PosSemidef := Matrix.PosSemidef.diagonal weight_nonneg
  exact hg.add hd.1

/-- Positive definite on ALL32 interior coordinates, before the three-color product. -/
theorem gram_posDef : gram.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos gram_hermitian
  intro f hf
  simpa only [star_trivial] using gram_positive f hf

end OperatorDerivativeRewrite.Foundation.FourCubeCompletedGram
