import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic

/-! Two finite-dimensional obstructions to incomplete energy-form arguments.
The diagonal models constants on a two-point probability space. Zero energy
does not make this starting domain dense. A finite tested sector also cannot
certify contraction on an untested orthogonal sector. -/
namespace OperatorDerivativeRewrite.Foundation.EnergySeedDensityObstruction
noncomputable section

def constantDomain : Set (ℝ × ℝ) := {x | x.1 = x.2}

theorem constantDomain_closed : IsClosed constantDomain :=
  isClosed_eq continuous_fst continuous_snd

theorem outside_constantDomain : ((0, 1) : ℝ × ℝ) ∉ constantDomain := by
  norm_num [constantDomain]

theorem constantDomain_not_dense : ¬ Dense constantDomain := by
  intro h
  have hm : ((0, 1) : ℝ × ℝ) ∈ closure constantDomain := by
    rw [h.closure_eq]
    trivial
  rw [constantDomain_closed.closure_eq] at hm
  exact outside_constantDomain hm

def zeroSeed (_ : constantDomain) : ℝ := 0

theorem zeroSeed_continuous : Continuous zeroSeed := continuous_const

theorem zeroSeed_graph_closed :
    IsClosed {p : (ℝ × ℝ) × ℝ | p.1 ∈ constantDomain ∧ p.2 = 0} := by
  exact (constantDomain_closed.preimage continuous_fst).inter
    (isClosed_eq continuous_snd continuous_const)

theorem zeroSeed_energy_vanishes (x : constantDomain) : zeroSeed x ^ 2 = 0 := by
  norm_num [zeroSeed]

def testEnergy (x : ℝ × ℝ) : ℝ := x.1 ^ 2 / 2 + 2 * x.2 ^ 2

def referenceEnergy (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

theorem tested_sector_contraction (x : ℝ × ℝ) (hx : x.2 = 0) :
    testEnergy x ≤ referenceEnergy x := by
  simp only [testEnergy, referenceEnergy, hx]
  nlinarith [sq_nonneg x.1]

theorem untested_sector_failure :
    referenceEnergy (0, 1) < testEnergy (0, 1) := by
  norm_num [testEnergy, referenceEnergy]

end
end OperatorDerivativeRewrite.Foundation.EnergySeedDensityObstruction
