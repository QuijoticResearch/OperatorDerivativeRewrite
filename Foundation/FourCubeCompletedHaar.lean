import Foundation.FourCubeExteriorSources
import Foundation.FourCubeDirichletHaar

/-! Actual32-link Haar completion: source-uniform control before the exterior scalar,
exact partition factorization and normalized density/observable identities. -/
noncomputable section
open MeasureTheory
namespace OperatorDerivativeRewrite.Foundation.FourCubeCompletedHaar
open QuaternionSU2Representation OneSidedBlockRank FourCubeHaarParity FourCubePinnedCoercivity
open FourCubeDirichletBox FourCubeNativeTransport FourCubeCoreIncident FourCubeExteriorSources

def diagonal (s : InteriorState) : ℝ :=
  ∑ e : Interior,(FourCubeNegativeCompletion.multiplicity e : ℝ)*defect (s e)
def completedAction (b : Fin 3 → SU2) (s : InteriorState) : ℝ := nativeAction b s+diagonal s
def sourceCost (b : Fin 3 → SU2) : ℝ := 3*defect (b 0)+4*defect (b 1)+3*defect (b 2)
def standardWeight (β : ℝ) (b : Fin 3 → SU2) (s : InteriorState) : ℝ := Real.exp (-β*action b s)
def completedWeight (β : ℝ) (b : Fin 3 → SU2) (s : InteriorState) : ℝ :=
  Real.exp (-β*completedAction b s)
def standardPartition (β : ℝ) (b : Fin 3 → SU2) : ℝ := ∫ s,standardWeight β b s ∂interiorHaar
def completedPartition (β : ℝ) (b : Fin 3 → SU2) : ℝ := ∫ s,completedWeight β b s ∂interiorHaar
def standardFreeEnergy (β : ℝ) (b : Fin 3 → SU2) : ℝ := -Real.log (standardPartition β b)
def completedFreeEnergy (β : ℝ) (b : Fin 3 → SU2) : ℝ := -Real.log (completedPartition β b)

attribute [local irreducible] faces retainedFaces coreFaces nativeFaces OneSidedBlockIncidence.edges

theorem action_split (b : Fin 3 → SU2) (s : InteriorState) :
    action b s=completedAction b s+sourceCost b := by
  simpa only [completedAction,diagonal,sourceCost,native_action_identity] using full_action_identity b s

theorem retained_sum (b : Fin 3 → SU2) (s : InteriorState) :
    (∑ p∈retainedFaces,defect (word b s p))=completedAction b s := by
  rw [retainedFaces,Finset.sum_union native_negative_disjoint]
  change nativeAction b s+FourCubeNegativeCompletion.negativeAction b s=completedAction b s
  rw [FourCubeNegativeCompletion.negative_action_identity]
  rfl

theorem isolation_retained (e : Interior) : isolation e∈retainedFaces := by
  rw [retained_eq_core,coreFaces]
  apply Finset.mem_filter.mpr
  refine ⟨isolation_mem e,⟨slot e,?_⟩⟩
  have hl := isolation_labels e (slot e)
  rw [if_pos rfl] at hl
  rw [← label_core_source _ e hl]
  exact core_embed e

/-- The ACTUAL completed action controls ALL32 links before any exterior source cost. -/
theorem completed_coercivity (b : Fin 3 → SU2) (s : InteriorState) :
    (∑ e : Interior,defect (s e)) ≤ completedAction b s := by
  classical
  let chosen : Finset BoxFace := Finset.univ.image isolation
  have hsub : chosen ⊆ retainedFaces := by
    intro p hp
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hp
    exact isolation_retained e
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p _ _ => defect_nonneg (word b s p))
  change (∑ p∈Finset.univ.image isolation,defect (word b s p)) ≤ _ at hs
  rw [Finset.sum_image (fun e _ f _ h => isolation_injective h)] at hs
  simpa only [isolation_defect,retained_sum] using hs

theorem completed_nonneg (b : Fin 3 → SU2) (s : InteriorState) : 0 ≤ completedAction b s :=
  (Finset.sum_nonneg (fun e _ => defect_nonneg (s e))).trans (completed_coercivity b s)

theorem completed_upper (b : Fin 3 → SU2) (s : InteriorState) : completedAction b s ≤ 240 := by
  rw [← retained_sum]
  calc
    _ ≤ ∑ _p∈retainedFaces,(2 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := (abs_le.mp (halfTrace_bound (word b s p))).1
      dsimp [defect]
      linarith
    _ = 240 := by rw [Finset.sum_const,retained_card]; norm_num

theorem completed_measurable (b : Fin 3 → SU2) : Measurable (completedAction b) := by
  have he : completedAction b=fun s => action b s-sourceCost b := by
    funext s
    rw [action_split]
    ring
  rw [he]
  exact (FourCubeDirichletHaar.action_measurable b).sub measurable_const

theorem weight_factor (β : ℝ) (b : Fin 3 → SU2) (s : InteriorState) :
    standardWeight β b s=Real.exp (-β*sourceCost b)*completedWeight β b s := by
  rw [standardWeight,completedWeight,action_split,← Real.exp_add]
  congr 1
  ring

theorem weight_reverse (β : ℝ) (b : Fin 3 → SU2) (s : InteriorState) :
    completedWeight β b s=Real.exp (β*sourceCost b)*standardWeight β b s := by
  rw [standardWeight,completedWeight,action_split,← Real.exp_add]
  congr 1
  ring

theorem standard_integrable (β : ℝ) (b : Fin 3 → SU2) :
    Integrable (standardWeight β b) interiorHaar := FourCubeDirichletHaar.boltzmann_integrable b β

theorem completed_integrable (β : ℝ) (b : Fin 3 → SU2) :
    Integrable (completedWeight β b) interiorHaar := by
  have he : completedWeight β b=fun s => Real.exp (β*sourceCost b)*standardWeight β b s :=
    funext (weight_reverse β b)
  rw [he]
  exact (standard_integrable β b).const_mul _

/-- Actual Haar partitions, with proved integrability for EVERY real coupling. -/
theorem partition_factor (β : ℝ) (b : Fin 3 → SU2) :
    standardPartition β b=Real.exp (-β*sourceCost b)*completedPartition β b := by
  unfold standardPartition completedPartition
  simp_rw [weight_factor]
  exact integral_const_mul _ _

theorem standard_positive (β : ℝ) (b : Fin 3 → SU2) : 0<standardPartition β b := by
  unfold standardPartition
  apply (integral_pos_iff_support_of_nonneg
    (fun s => (Real.exp_pos _).le) (standard_integrable β b)).mpr
  have hs : Function.support (standardWeight β b)=Set.univ := by
    ext s
    simp [Function.mem_support,standardWeight,Real.exp_ne_zero]
  change 0 < interiorHaar (Function.support (standardWeight β b))
  rw [hs]
  simp

theorem completed_positive (β : ℝ) (b : Fin 3 → SU2) : 0<completedPartition β b := by
  have h := standard_positive β b
  rw [partition_factor] at h
  by_contra hn
  have hh := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-β*sourceCost b)).le
    (le_of_not_gt hn)
  linarith

theorem free_energy_split (β : ℝ) (b : Fin 3 → SU2) :
    standardFreeEnergy β b=β*sourceCost b+completedFreeEnergy β b := by
  unfold standardFreeEnergy completedFreeEnergy
  rw [partition_factor,Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (completed_positive β b)),
    Real.log_exp]
  ring

/-- Equality of actual normalized Haar densities; the diagonal penalty is retained. -/
theorem normalized_density (β : ℝ) (b : Fin 3 → SU2) (s : InteriorState) :
    standardWeight β b s/standardPartition β b=
      completedWeight β b s/completedPartition β b := by
  rw [weight_factor,partition_factor]
  field_simp [Real.exp_ne_zero,ne_of_gt (completed_positive β b)]

/-- Genuine integrable observable domain, with both convergence and normalized equality. -/
theorem observable_identification (β : ℝ) (b : Fin 3 → SU2) (f : InteriorState → ℝ)
    (hf : Integrable (fun s => f s*completedWeight β b s) interiorHaar) :
    Integrable (fun s => f s*standardWeight β b s) interiorHaar ∧
      (∫ s,f s*standardWeight β b s ∂interiorHaar)/standardPartition β b=
        (∫ s,f s*completedWeight β b s ∂interiorHaar)/completedPartition β b := by
  have he : (fun s => f s*standardWeight β b s)=
      fun s => Real.exp (-β*sourceCost b)*(f s*completedWeight β b s) := by
    funext s
    rw [weight_factor]
    ring
  constructor
  · rw [he]
    exact hf.const_mul _
  · rw [he,integral_const_mul,partition_factor]
    field_simp [Real.exp_ne_zero,ne_of_gt (completed_positive β b)]

def angles (x y z : ℝ) : Fin 3 → SU2 :=
  ![SU2JointPlaquetteCubic.axis 0 x,(SU2JointPlaquetteCubic.axis 1 y)⁻¹,
    (SU2JointPlaquetteCubic.axis 2 z)⁻¹]

theorem sourceCost_angles (x y z : ℝ) : sourceCost (angles x y z)=
    3*(1-Real.cos x)+4*(1-Real.cos y)+3*(1-Real.cos z) := by
  simp only [sourceCost,angles,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    defect_inv,axis_defect]

theorem sourceCost_reversal (x y z : ℝ) :
    sourceCost (angles (-x) (-y) (-z))=sourceCost (angles x y z) := by
  rw [sourceCost_angles,sourceCost_angles]
  simp only [Real.cos_neg]

/-- Exact odd free-energy reduction, with no derivative/limit interchange. -/
theorem odd_free_energy (β x y z : ℝ) :
    standardFreeEnergy β (angles x y z)-standardFreeEnergy β (angles (-x) (-y) (-z))=
      completedFreeEnergy β (angles x y z)-completedFreeEnergy β (angles (-x) (-y) (-z)) := by
  rw [free_energy_split,free_energy_split,sourceCost_reversal]
  ring

end OperatorDerivativeRewrite.Foundation.FourCubeCompletedHaar
