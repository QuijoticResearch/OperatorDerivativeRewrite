import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Field

/-! Scalar heat damping on one spectral shell preserves every normalized
angular share and its anisotropy. No nonlinear transfer is assumed. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.NormalizedShellHeat
variable {ι : Type*} [Fintype ι]

def total (E : ι → ℝ) : ℝ := ∑ j, E j
def share (E : ι → ℝ) (j : ι) : ℝ := E j / total E
def excess (E : ι → ℝ) (j : ι) : ℝ := share E j - 1/(Fintype.card ι : ℝ)
def anisotropy (E : ι → ℝ) : ℝ := ∑ j, (excess E j)^2
def heat (nu frequency t : ℝ) (E : ι → ℝ) (j : ι) : ℝ :=
  Real.exp (-2*nu*frequency*t)*E j

theorem total_scale (c : ℝ) (E : ι → ℝ) :
    total (fun j => c*E j) = c*total E := by simp [total, Finset.mul_sum]

theorem share_scale (c : ℝ) (hc : c ≠ 0) (E : ι → ℝ) (j : ι) :
    share (fun j => c*E j) j = share E j := by
  rw [share, total_scale]
  exact mul_div_mul_left (E j) (total E) hc

theorem heat_share (nu frequency t : ℝ) (E : ι → ℝ) (j : ι) :
    share (heat nu frequency t E) j = share E j :=
  share_scale _ (ne_of_gt (Real.exp_pos _)) E j

theorem heat_excess (nu frequency t : ℝ) (E : ι → ℝ) (j : ι) :
    excess (heat nu frequency t E) j = excess E j := by
  simp only [excess, heat_share]

theorem heat_anisotropy (nu frequency t : ℝ) (E : ι → ℝ) :
    anisotropy (heat nu frequency t E) = anisotropy E := by
  simp only [anisotropy, heat_excess]

end OperatorDerivativeRewrite.Foundation.NormalizedShellHeat
