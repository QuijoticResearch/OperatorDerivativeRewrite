import Foundation.PeriodicFineSparseGram

/-! A nonzero checkerboard coarse field whose raw fine lift is an actual physical eigenvector. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicCheckerboardPhysical
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarsePhysicalSector PeriodicCorrectedPhysicalLift
open PeriodicFinePhysicalGreen PeriodicFineEnergyWitnessCertificates PeriodicFineSparseGram
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def coarseZ (e : CoarseEdge) : ℤ :=
  characterZ Finset.univ e.1 * (if e.2 = 0 then 1 else if e.2 = 1 then -1 else 0)

def liftZ (e : Edge) : ℤ := if oddEdge e then coarseZ (coarseBlock e.1,e.2) else 0

def source (e : CoarseEdge) : ℝ := (coarseZ e : ℝ)
def lift (e : Edge) : ℝ := (liftZ e : ℝ)

set_option maxHeartbeats 32000000 in
-- Kernel reduction checks the six-pair stencil on all 1024 actual fine edges.
theorem gram_certificate : ∀ e : Edge, stencil liftZ e = 8 * liftZ e := by decide

theorem gram_lift : G lift = (8 : ℝ) • lift := by
  change G (fun e => (liftZ e : ℝ)) = (8 : ℝ) • lift
  rw [G_cast]
  funext e
  change (intGram liftZ e : ℝ) = 8 * (liftZ e : ℝ)
  have h : intGram liftZ e = 8 * liftZ e := by
    rw [intGram_stencil]
    exact gram_certificate e
  exact_mod_cast h

theorem lift_flat : lift = flatLift source := by
  funext e
  rw [flatLift_apply]
  by_cases h : oddEdge e <;> simp [lift, liftZ, source, h]

theorem lift_physical : lift ∈ fineSpace := by
  have h := fineSpace.smul_mem (1/8 : ℝ) (gram_mem_physical lift)
  rw [gram_lift, smul_smul] at h
  norm_num at h
  exact h

theorem average_lift : average lift = source := by rw [lift_flat, average_flatLift]

theorem source_physical : source ∈ physicalSpace := by
  rw [← average_lift]
  exact average_physical lift lift_physical

def physicalSource : physicalSpace := ⟨source,source_physical⟩

theorem source_nonzero : source ≠ 0 := by
  intro h
  have he := congrFun h ((fun _ => 0),0)
  norm_num [source, coarseZ, characterZ] at he

theorem physicalSource_nonzero : physicalSource ≠ 0 := by
  intro h
  exact source_nonzero (congrArg Subtype.val h)

set_option maxHeartbeats 16000000 in
-- Kernel reduction sums the integer squares over all 64 coarse edges.
theorem coarse_size_certificate : (∑ e : CoarseEdge, coarseZ e * coarseZ e) = (32 : ℤ) := by decide

set_option maxHeartbeats 16000000 in
-- Kernel reduction sums the integer squares over all 1024 fine edges.
theorem fine_size_certificate : (∑ e : Edge, liftZ e * liftZ e) = (256 : ℤ) := by decide

theorem lift_size : PeriodicPhysicalLiftMinimum.fineSize lift = 256 := by
  unfold PeriodicPhysicalLiftMinimum.fineSize dotProduct lift
  exact_mod_cast fine_size_certificate

end OperatorDerivativeRewrite.Foundation.PeriodicCheckerboardPhysical
