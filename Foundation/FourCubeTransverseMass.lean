import Foundation.FourCubeCompletedGram

/-! Exact transverse mass in the smallest frozen-exterior4D cell.
This is a finite-cell identity, not a volume-uniform physical mass gap. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FourCubeTransverseMass
open OneSidedBlockIncidence OneSidedBlockRank OneSidedCapComplex
open FourCubeHaarParity FourCubeHaarChannels FourCubePinnedCoercivity
open FourCubeNativeTransport FourCubeCompletedHaar

attribute [local irreducible] edges innerFaces upperFaces

abbrev UpperFiber (e : Interior) := {j : Fin 4 // j≠e.val.2 ∧ e.val.1 j=1}
def positiveMultiplicity (e : Interior) : ℕ := Fintype.card (UpperFiber e)

def upperFiberEquiv : Upper ≃ Σ e : Interior,UpperFiber e where
  toFun p := by
    have hp : p.val.1∈edges ∧ p.val.2≠p.val.1.2 ∧ p.val.1.1 p.val.2=1 := by
      simpa only [upperFaces,Finset.mem_filter,Finset.mem_univ,true_and] using p.property
    exact ⟨ribbonInterior p,⟨p.val.2,hp.2.1,hp.2.2⟩⟩
  invFun q := ⟨(q.1.val,q.2.val),by
    simp only [upperFaces,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨q.1.property,q.2.property⟩⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv := by rintro ⟨⟨e,he⟩,⟨j,hj⟩⟩; rfl

theorem transverse_count : ∀ e : Interior,
    positiveMultiplicity e+FourCubeNegativeCompletion.multiplicity e=3 := by decide +kernel


theorem upper_sum (h : Interior → ℝ) :
    (∑ p : Upper,h (ribbonInterior p))=∑ e : Interior,(positiveMultiplicity e : ℝ)*h e := by
  calc
    _ = ∑ q : (Σ e : Interior,UpperFiber e),h q.1 :=
      Fintype.sum_equiv upperFiberEquiv _ _ (fun _ => rfl)
    _ = ∑ e : Interior,∑ _j : UpperFiber e,h e := by rw [Fintype.sum_sigma]
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,positiveMultiplicity]

/-- Upper and lower transverse fibers partition all three transverse directions. -/
theorem transverse_sum (h : Interior → ℝ) :
    (∑ p : Upper,h (ribbonInterior p))+
      (∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*h e)=
      3*∑ e : Interior,h e := by
  rw [upper_sum,← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [← add_mul]
  congr 1
  exact_mod_cast transverse_count e

/-- Actual nonlinear vacuum completion; all32 links remain unpinned. -/
theorem vacuum_mass (s : InteriorState) :
    completedAction (fun _ => 1) s=internalAction s+3*∑ e : Interior,defect (s e) := by
  have hb : boundary (fun _ => 1)=fun _ => 1 := by
    funext c
    simp [boundary_formula]
  unfold completedAction
  rw [native_action_identity,hb]
  change vacuumAction s+diagonal s=internalAction s+3*∑ e : Interior,defect (s e)
  rw [vacuum_decomposition]
  have hf := transverse_sum (fun e => defect (s e))
  change ribbonEnergy s+diagonal s=3*∑ e : Interior,defect (s e) at hf
  linarith

def innerEnergy (f : OneSidedBlockRank.Field) : ℝ :=
  ∑ p : Inner,(realCurl (extend f) p.val)^2

theorem real_energy_split (f : OneSidedBlockRank.Field) :
    realEnergy (extend f)=innerEnergy f+∑ p : Upper,(f (ribbonInterior p))^2 := by
  rw [realEnergy,← Finset.sum_coe_sort innerFaces,← Finset.sum_coe_sort upperFaces]
  unfold innerEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have h : extend f p.val.1=f (ribbonInterior p) := extend_on f (ribbonInterior p)
  rw [h]

/-- Exact quadratic identity, stronger than positive definiteness alone. -/
theorem quadratic_mass (f : OneSidedBlockRank.Field) :
    FourCubeCompletedGram.quadratic f=innerEnergy f+3*∑ e : Interior,(f e)^2 := by
  unfold FourCubeCompletedGram.quadratic
  rw [real_energy_split]
  have hf := transverse_sum (fun e => (f e)^2)
  change (∑ p : Upper,(f (ribbonInterior p))^2)+FourCubeCompletedGram.penalty f=
    3*∑ e : Interior,(f e)^2 at hf
  linarith

/-- This quantitative bound is for the specific32-link frozen-exterior matrix. -/
theorem gram_lower_three (f : OneSidedBlockRank.Field) :
    3*(∑ e : Interior,(f e)^2) ≤ dotProduct f (FourCubeCompletedGram.gram.mulVec f) := by
  rw [FourCubeCompletedGram.gram_energy,quadratic_mass]
  have h : 0 ≤ innerEnergy f := Finset.sum_nonneg (fun p _ => sq_nonneg _)
  linarith

end OperatorDerivativeRewrite.Foundation.FourCubeTransverseMass
