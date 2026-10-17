import Foundation.PeriodicCheckerboardPhysical

/-! Exact integer certificates for an inactive-direction three-mask mode on
the actual side-four/side-two periodic lattice. No Fourier symbol assumed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicThreeMaskCertificates
open PeriodicInteriorGaugeKernel PeriodicCoarseAveraging PeriodicCoarseGaugeDiagnostics
open PeriodicCoarseWalshBasis PeriodicFineSparseGram
set_option maxRecDepth 65536

def sourceZ : CoarseEdge → ℤ := modeZ ({0, 1, 2}, 3)
def wZ : Edge → ℤ := flatLiftZ sourceZ
def gZ : Edge → ℤ := stencil wZ
def hZ : Edge → ℤ := stencil gZ
def pZ (e : Edge) : ℤ := 16 * gZ e - hZ e
def zZ (e : Edge) : ℤ := 49 * gZ e - 4 * hZ e

def aZ (e : Edge) : ℤ := sourceZ (coarseBlock e.1, e.2)

set_option maxHeartbeats 128000000 in
-- Kernel reduction checks the actual fine edges.
theorem a_certificate : ∀ e : Edge, stencil aZ e = 6 * aZ e := by decide

def explicitG (e : Edge) : ℤ :=
  if e.2 = 3 then 6 * wZ e
  else if fineBits e.1 e.2 = 1 then
    -2 * sourceZ (coarseBlock e.1, 3) * (if fineBits e.1 3 = 1 then 1 else -1)
  else 0

set_option maxHeartbeats 128000000 in
-- Kernel reduction identifies the one-stencil closed formula.
theorem g_formula : gZ = explicitG := by
  funext e
  have h : ∀ u : Edge, gZ u = explicitG u := by decide
  exact h e

set_option maxHeartbeats 128000000 in
-- Kernel reduction checks one stencil per edge after the explicit identification.
theorem g_certificate : ∀ e : Edge, stencil gZ e = 10 * gZ e - 12 * aZ e := by
  rw [g_formula]
  decide

set_option maxHeartbeats 128000000 in
-- Kernel reduction checks the 64 coarse edges.
theorem average_a_certificate : ∀ q : CoarseEdge,
    averageZ aZ q = 8 * sourceZ q := by decide

set_option maxHeartbeats 128000000 in
-- Kernel reduction uses the explicit one-stencil field.
theorem average_g_certificate : ∀ q : CoarseEdge,
    averageZ gZ q = 48 * sourceZ q := by
  rw [g_formula]
  decide

theorem stencil_linear (a b : ℤ) (f g : Edge → ℤ) (e : Edge) :
    stencil (fun u => a * f u + b * g u) e = a * stencil f e + b * stencil g e := by
  simp_rw [← intGram_stencil]
  simp only [PeriodicFineEnergyWitnessCertificates.intGram, intCurl]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem average_linear (a b : ℤ) (f g : Edge → ℤ) (q : CoarseEdge) :
    averageZ (fun u => a * f u + b * g u) q = a * averageZ f q + b * averageZ g q := by
  unfold averageZ
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h : v q.2 = 1 <;> simp [h]

theorem p_formula : pZ = fun e => 6 * gZ e + 12 * aZ e := by
  funext e
  simp only [pZ, hZ, g_certificate]
  ring

theorem z_formula : zZ = fun e => 9 * gZ e + 48 * aZ e := by
  funext e
  simp only [zZ, hZ, g_certificate]
  ring

theorem projection_certificate : ∀ e : Edge, stencil pZ e = 60 * gZ e := by
  intro e
  rw [p_formula, stencil_linear, g_certificate, a_certificate]
  ring

theorem green_certificate : ∀ e : Edge, stencil zZ e = 15 * pZ e := by
  intro e
  rw [z_formula, stencil_linear, g_certificate, a_certificate, p_formula]
  ring

theorem projection_average_certificate : ∀ q : CoarseEdge,
    averageZ pZ q = 384 * sourceZ q := by
  intro q
  rw [p_formula, average_linear, average_g_certificate, average_a_certificate]
  ring

theorem green_average_certificate : ∀ q : CoarseEdge,
    averageZ zZ q = 816 * sourceZ q := by
  intro q
  rw [z_formula, average_linear, average_g_certificate, average_a_certificate]
  ring

end OperatorDerivativeRewrite.Foundation.PeriodicThreeMaskCertificates
