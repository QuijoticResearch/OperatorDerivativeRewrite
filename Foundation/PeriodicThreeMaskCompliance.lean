import Foundation.PeriodicThreeMaskCertificates
import Foundation.PeriodicCheckerboardCompliance

/-! Actual Hodge and Green identification for the three-mask mode, yielding
a compliance eigenvalue strictly below the checkerboard value. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicThreeMaskCompliance
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseCurl
open PeriodicCoarseWalshBasis PeriodicCoarsePhysicalSector PeriodicFinePhysicalGreen
open PeriodicProjectedCoarseLift PeriodicProjectedCoarseRange PeriodicEnergySchur
open PeriodicCoarseGaugeDiagnostics PeriodicCorrectedPhysicalLift
open PeriodicFineSparseGram
open PeriodicFineEnergyWitnessCertificates hiding wZ pZ aZ
open PeriodicThreeMaskCertificates
set_option maxRecDepth 65536
set_option backward.isDefEq.respectTransparency false

def source (e : CoarseEdge) : ℝ := (sourceZ e : ℝ)
def w (e : Edge) : ℝ := (wZ e : ℝ)
def p : Edge → ℝ := G ((1/480 : ℝ) • ((16 : ℝ) • w - G w))
def z : Edge → ℝ := G ((1/7200 : ℝ) • ((49 : ℝ) • w - (4 : ℝ) • G w))
def sixMode (e : Edge) : ℝ := (aZ e : ℝ)
def tenMode : Edge → ℝ := G w - (3 : ℝ) • sixMode

theorem gram_cast_stencil (f : Edge → ℤ) :
    G (fun e => (f e : ℝ)) = fun e => (stencil f e : ℝ) := by
  rw [G_cast]
  exact funext (fun e => congrArg (fun n : ℤ => (n : ℝ)) (intGram_stencil f e))

theorem gram_w : G w = fun e => (gZ e : ℝ) := gram_cast_stencil wZ

theorem gram_sixMode : G sixMode = (6 : ℝ) • sixMode := by
  change G (fun e => (aZ e : ℝ)) = (6 : ℝ) • sixMode
  rw [gram_cast_stencil]
  funext e
  simp only [a_certificate, Int.cast_mul, Int.cast_ofNat, Pi.smul_apply,
    smul_eq_mul, sixMode]

theorem gram_tenMode : G tenMode = (10 : ℝ) • tenMode := by
  rw [tenMode, map_sub, map_smul, gram_sixMode, gram_w, gram_cast_stencil]
  funext e
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, g_certificate, Int.cast_sub,
    Int.cast_mul, Int.cast_ofNat, sixMode]
  ring

theorem frequency_orthogonal : dotProduct sixMode tenMode = 0 := by
  have h := gram_symmetric sixMode tenMode
  rw [gram_sixMode, gram_tenMode, dotProduct_smul, smul_dotProduct] at h
  simp only [smul_eq_mul] at h
  nlinarith

theorem sixMode_nonzero : sixMode ≠ 0 := by
  intro h
  have he := congrFun h ((fun _ => 0), 3)
  have ha : aZ ((fun _ => 0), 3) = 1 := by decide
  change (aZ ((fun _ => 0), 3) : ℝ) = 0 at he
  rw [ha] at he
  norm_num at he

theorem tenMode_nonzero : tenMode ≠ 0 := by
  intro h
  have he := congrFun h ((fun _ => 0), 3)
  have ha : aZ ((fun _ => 0), 3) = 1 := by decide
  have hg : gZ ((fun _ => 0), 3) = 0 := by decide
  change (G w) ((fun _ => 0), 3) - 3 * (aZ ((fun _ => 0), 3) : ℝ) = 0 at he
  rw [gram_w] at he
  change (gZ ((fun _ => 0), 3) : ℝ) - 3 * (aZ ((fun _ => 0), 3) : ℝ) = 0 at he
  rw [hg, ha] at he
  norm_num at he

theorem p_cast : p = (1/480 : ℝ) • (fun e => (pZ e : ℝ)) := by
  rw [p, map_smul, map_sub, map_smul, gram_w, gram_cast_stencil]
  funext e
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, pZ, hZ, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat]

theorem p_frequency_decomposition :
    p = (1/16 : ℝ) • sixMode + (1/80 : ℝ) • tenMode := by
  rw [p_cast, p_formula]
  funext e
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul, Int.cast_add,
    Int.cast_mul, Int.cast_ofNat, sixMode, tenMode, gram_w]
  ring

theorem z_cast : z = (1/7200 : ℝ) • (fun e => (zZ e : ℝ)) := by
  rw [z, map_smul, map_sub, map_smul, map_smul, gram_w, gram_cast_stencil]
  funext e
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, zZ, hZ, Int.cast_sub, Int.cast_mul,
    Int.cast_ofNat]

theorem w_flat : w = flatLift source := (flatLift_cast sourceZ).symm

theorem gram_p : G p = G (normalizedLift source) := by
  have hr : normalizedLift source = (1/8 : ℝ) • w := by
    rw [normalizedLift, LinearMap.smul_apply, ← w_flat]
  rw [hr, map_smul, gram_w, p_cast, map_smul, gram_cast_stencil]
  funext e
  simp only [Pi.smul_apply, smul_eq_mul, projection_certificate, Int.cast_mul, Int.cast_ofNat]
  ring

theorem gram_z : G z = p := by
  rw [z_cast, p_cast, map_smul, gram_cast_stencil]
  funext e
  simp only [Pi.smul_apply, smul_eq_mul, green_certificate, Int.cast_mul, Int.cast_ofNat]
  ring

theorem p_physical : p ∈ fineSpace := gram_mem_physical _
theorem z_physical : z ∈ fineSpace := gram_mem_physical _

theorem average_p : average p = (1/10 : ℝ) • source := by
  rw [p_cast, map_smul]
  funext q
  simp only [Pi.smul_apply, smul_eq_mul, average_cast, projection_average_certificate,
    Int.cast_mul, Int.cast_ofNat, source]
  ring

theorem average_z : average z = (17/1200 : ℝ) • source := by
  rw [z_cast, map_smul]
  funext q
  simp only [Pi.smul_apply, smul_eq_mul, average_cast, green_average_certificate,
    Int.cast_mul, Int.cast_ofNat, source]
  ring

theorem source_physical : source ∈ physicalSpace := by
  have ha := average_physical p p_physical
  have h := physicalSpace.smul_mem (10 : ℝ) ha
  rw [average_p, smul_smul] at h
  norm_num at h
  exact h

def physicalSource : physicalSpace := ⟨source, source_physical⟩
def fineP : fineSpace := ⟨p, p_physical⟩
def fineZ : fineSpace := ⟨z, z_physical⟩

theorem projected_lift : projectedLift source = p := by
  have hg : G (p - normalizedLift source) = 0 := by rw [map_sub, gram_p, sub_self]
  have he : fineEnergy (p - normalizedLift source) = 0 := by
    rw [← gram_energy, hg, dotProduct_zero]
  have hi := (fineEnergy_zero_iff _).mp he
  rw [map_sub, sub_eq_zero] at hi
  have hc : incidence (p - projectedLift source) = 0 := by
    rw [map_sub, hi, projectedLift_incidence, sub_self]
  have hp : p - projectedLift source ∈ fineSpace :=
    fineSpace.sub_mem p_physical (projectedLift_physical source)
  exact (sub_eq_zero.mp (dotProduct_self_eq_zero.mp (hp _ hc))).symm

theorem B_source : B physicalSource = fineP := Subtype.ext projected_lift

theorem Green_fineP : Green fineP = fineZ := by
  apply physicalGram_injective
  apply Subtype.ext
  change G (Green fineP).val = G z
  rw [Green_equation, gram_z]
  rfl

theorem Q_source : physicalCompression physicalSource = (1/10 : ℝ) • physicalSource := by
  apply Subtype.ext
  change average (projectedLift source) = (1/10 : ℝ) • source
  rw [projected_lift, average_p]

theorem S_source : S physicalSource = (17/1200 : ℝ) • physicalSource := by
  rw [S_apply, B_source, Green_fineP]
  exact Subtype.ext average_z

theorem energy_multiplier : energyMultiplier physicalSource = (1200/17 : ℝ) • physicalSource := by
  apply S_injective
  have he : S (energyMultiplier physicalSource) = physicalSource :=
    schurEquiv.apply_symm_apply physicalSource
  rw [he, map_smul, S_source, smul_smul]
  norm_num

theorem source_squared_size : dotProduct source source = 16 := by
  have h := mode_pair ({0, 1, 2}, 3) ({0, 1, 2}, 3)
  change dotProduct (mode ({0, 1, 2}, 3)) (mode ({0, 1, 2}, 3)) = 16
  simpa using h

theorem physicalSource_nonzero : physicalSource ≠ 0 := by
  intro h
  have hs : source = 0 := congrArg Subtype.val h
  have hn := source_squared_size
  rw [hs, dotProduct_zero] at hn
  norm_num at hn

theorem compliance_below_checker :
    dotProduct physicalSource.val (S physicalSource).val <
      (1/64 : ℝ) * dotProduct physicalSource.val physicalSource.val := by
  rw [S_source]
  change dotProduct source ((17/1200 : ℝ) • source) < (1/64 : ℝ) * dotProduct source source
  rw [dotProduct_smul, source_squared_size]
  norm_num

theorem no_checker_lower_bound :
    ¬ ∀ c : physicalSpace,
      (1/64 : ℝ) * dotProduct c.val c.val ≤ dotProduct c.val (S c).val := by
  intro h
  exact (not_le_of_gt compliance_below_checker) (h physicalSource)

theorem constrained_minimum_value : fineEnergy (energyLift physicalSource).val =
    (19200/17 : ℝ) := by
  rw [energyLift_value, energy_multiplier]
  change dotProduct source ((1200/17 : ℝ) • source) = _
  rw [dotProduct_smul, source_squared_size]
  norm_num

theorem curvature_above_checker :
    (64 : ℝ) * dotProduct physicalSource.val physicalSource.val <
      dotProduct physicalSource.val (energyMultiplier physicalSource).val := by
  rw [energy_multiplier]
  change (64 : ℝ) * dotProduct source source < dotProduct source ((1200/17 : ℝ) • source)
  rw [dotProduct_smul, source_squared_size]
  norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicThreeMaskCompliance
