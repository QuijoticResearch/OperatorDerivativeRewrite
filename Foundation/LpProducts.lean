import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Products with their actual integrability exponents

Hölder gives L² × L² → L¹, L⁴ × L⁴ → L², and L∞ × L² → L².
These facts do not imply closure of an operator domain under multiplication.
All results below hold for arbitrary measures. Inner products are real-valued.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace OperatorDerivativeRewrite.Foundation

variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {p q r : ℝ≥0∞}

/-- Arithmetic for the L⁴ × L⁴ → L² specialization of Hölder. -/
instance holderTripleFourFourTwo : ENNReal.HolderTriple 4 4 2 where
  inv_add_inv_eq_inv := by
    have h42 : (4 : ENNReal) = 2 * 2 := by norm_num
    rw [h42, ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl (ENNReal.natCast_ne_top 2)),
      ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero (ENNReal.natCast_ne_top 2),
      one_mul]

/-- Scalar products have the Hölder output exponent, rather than the input exponent. -/
theorem mul_memLp [ENNReal.HolderTriple p q r] {f g : Ω → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) : MemLp (fun ω ↦ f ω * g ω) r μ :=
  hf.fun_mul hg

/-- Vector-valued scalar multiplication has the same Hölder exponents. -/
theorem smul_memLp [ENNReal.HolderTriple p q r] {f : Ω → ℝ} {u : Ω → H}
    (hf : MemLp f p μ) (hu : MemLp u q μ) : MemLp (fun ω ↦ f ω • u ω) r μ :=
  hf.smul hu

/-- The pointwise inner product obeys Hölder, using pointwise Cauchy–Schwarz. -/
theorem inner_memLp [ENNReal.HolderTriple p q r] {u v : Ω → H}
    (hu : MemLp u p μ) (hv : MemLp v q μ) :
    MemLp (fun ω ↦ inner ℝ (u ω) (v ω)) r μ := by
  apply hu.of_bilin (inner ℝ) 1 hv continuous_inner
  exact Filter.Eventually.of_forall fun ω ↦ by
    simpa using nnnorm_inner_le_nnnorm (u ω) (v ω)

theorem mul_eLpNorm_le [ENNReal.HolderTriple p q r] {f g : Ω → ℝ}
    (hf : MemLp f p μ) (hg : MemLp g q μ) :
    eLpNorm (fun ω ↦ f ω * g ω) r μ ≤ eLpNorm f p μ * eLpNorm g q μ :=
  eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hg.aestronglyMeasurable

theorem smul_eLpNorm_le [ENNReal.HolderTriple p q r] {f : Ω → ℝ} {u : Ω → H}
    (hf : MemLp f p μ) (hu : MemLp u q μ) :
    eLpNorm (fun ω ↦ f ω • u ω) r μ ≤ eLpNorm f p μ * eLpNorm u q μ :=
  eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hu.aestronglyMeasurable

theorem inner_eLpNorm_le [ENNReal.HolderTriple p q r] {u v : Ω → H}
    (hu : MemLp u p μ) (hv : MemLp v q μ) :
    eLpNorm (fun ω ↦ inner ℝ (u ω) (v ω)) r μ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  simpa using eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm (inner ℝ) 1 continuous_inner
    hu.aestronglyMeasurable hv.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by simpa using @norm_inner_le_norm ℝ H _ _ _ (u ω) (v ω))

/-- Product on Mathlib's a.e. equivalence classes, with a Hölder output exponent. -/
def lpMul [ENNReal.HolderTriple p q r] (f : Lp ℝ p μ) (g : Lp ℝ q μ) : Lp ℝ r μ :=
  (mul_memLp (Lp.memLp f) (Lp.memLp g)).toLp _

def lpSmul [ENNReal.HolderTriple p q r] (f : Lp ℝ p μ) (u : Lp H q μ) : Lp H r μ :=
  (smul_memLp (Lp.memLp f) (Lp.memLp u)).toLp _

def lpInner [ENNReal.HolderTriple p q r] (u : Lp H p μ) (v : Lp H q μ) : Lp ℝ r μ :=
  (inner_memLp (Lp.memLp u) (Lp.memLp v)).toLp _

theorem lpMul_coeFn [ENNReal.HolderTriple p q r] (f : Lp ℝ p μ) (g : Lp ℝ q μ) :
    lpMul (r := r) f g =ᵐ[μ] fun ω ↦ f ω * g ω := MemLp.coeFn_toLp _

theorem lpSmul_coeFn [ENNReal.HolderTriple p q r] (f : Lp ℝ p μ) (u : Lp H q μ) :
    lpSmul (r := r) f u =ᵐ[μ] fun ω ↦ f ω • u ω := MemLp.coeFn_toLp _

theorem lpInner_coeFn [ENNReal.HolderTriple p q r] (u : Lp H p μ) (v : Lp H q μ) :
    lpInner (r := r) u v =ᵐ[μ] fun ω ↦ inner ℝ (u ω) (v ω) := MemLp.coeFn_toLp _

theorem lpMul_norm_le [ENNReal.HolderTriple p q r] (f : Lp ℝ p μ) (g : Lp ℝ q μ) :
    ‖lpMul (r := r) f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [lpMul, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness [Lp.memLp f, Lp.memLp g])
    (mul_eLpNorm_le (Lp.memLp f) (Lp.memLp g))

theorem lpSmul_norm_le [ENNReal.HolderTriple p q r] (f : Lp ℝ p μ) (u : Lp H q μ) :
    ‖lpSmul (r := r) f u‖ ≤ ‖f‖ * ‖u‖ := by
  rw [lpSmul, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness [Lp.memLp f, Lp.memLp u])
    (smul_eLpNorm_le (Lp.memLp f) (Lp.memLp u))

theorem lpInner_norm_le [ENNReal.HolderTriple p q r] (u : Lp H p μ) (v : Lp H q μ) :
    ‖lpInner (r := r) u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [lpInner, Lp.norm_toLp, Lp.norm_def, Lp.norm_def, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (by finiteness [Lp.memLp u, Lp.memLp v])
    (inner_eLpNorm_le (Lp.memLp u) (Lp.memLp v))

/-- L² scalar pairings are integrable; they need not be square-integrable. -/
theorem mul_L2_integrable {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun ω ↦ f ω * g ω) μ := memLp_one_iff_integrable.mp (mul_memLp hf hg)

theorem inner_L2_integrable {u v : Ω → H} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun ω ↦ inner ℝ (u ω) (v ω)) μ :=
  memLp_one_iff_integrable.mp (inner_memLp hu hv)

/-- Explicit specializations record the restricted L²-valued operations. -/
theorem mul_L4_memLp_two {f g : Ω → ℝ} (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    MemLp (fun ω ↦ f ω * g ω) 2 μ := mul_memLp hf hg

theorem smul_L4_memLp_two {f : Ω → ℝ} {u : Ω → H}
    (hf : MemLp f 4 μ) (hu : MemLp u 4 μ) :
    MemLp (fun ω ↦ f ω • u ω) 2 μ := smul_memLp hf hu

theorem inner_L4_memLp_two {u v : Ω → H} (hu : MemLp u 4 μ) (hv : MemLp v 4 μ) :
    MemLp (fun ω ↦ inner ℝ (u ω) (v ω)) 2 μ := inner_memLp hu hv

theorem mul_Linfty_L2_memLp_two {f g : Ω → ℝ}
    (hf : MemLp f ∞ μ) (hg : MemLp g 2 μ) :
    MemLp (fun ω ↦ f ω * g ω) 2 μ := mul_memLp hf hg

theorem smul_Linfty_L2_memLp_two {f : Ω → ℝ} {u : Ω → H}
    (hf : MemLp f ∞ μ) (hu : MemLp u 2 μ) :
    MemLp (fun ω ↦ f ω • u ω) 2 μ := smul_memLp hf hu

theorem inner_Linfty_L2_memLp_two {u v : Ω → H}
    (hu : MemLp u ∞ μ) (hv : MemLp v 2 μ) :
    MemLp (fun ω ↦ inner ℝ (u ω) (v ω)) 2 μ := inner_memLp hu hv

/-- The Hilbert-space pairing is the integral of the L¹ pointwise pairing. -/
theorem L2_inner_eq_integral (u v : Lp H 2 μ) :
    inner ℝ u v = ∫ ω, inner ℝ (u ω) (v ω) ∂μ := L2.inner_def u v

/-- Scalar–vector L² products have an L¹ output. -/
theorem smul_L2_memLp_one {f : Ω → ℝ} {u : Ω → H}
    (hf : MemLp f 2 μ) (hu : MemLp u 2 μ) :
    MemLp (fun ω ↦ f ω • u ω) 1 μ := smul_memLp hf hu

/-- Integrated Cauchy–Schwarz, with the actual L² norms. -/
theorem L2_integral_inner_bound (u v : Lp H 2 μ) :
    ‖∫ ω, inner ℝ (u ω) (v ω) ∂μ‖ ≤ ‖u‖ * ‖v‖ := by
  rw [← L2_inner_eq_integral]
  exact @norm_inner_le_norm ℝ (Lp H 2 μ) _ _ _ u v

/-- A real essentially bounded multiplier is symmetric on the L² Hilbert space. -/
theorem L2_bounded_multiplier_selfadj (f : Lp ℝ ∞ μ) (u v : Lp H 2 μ) :
    inner ℝ (lpSmul (r := 2) f u) v = inner ℝ u (lpSmul (r := 2) f v) := by
  rw [L2_inner_eq_integral, L2_inner_eq_integral]
  apply integral_congr_ae
  filter_upwards [lpSmul_coeFn (r := 2) f u, lpSmul_coeFn (r := 2) f v] with ω hu hv
  rw [hu, hv]
  simp only [real_inner_smul_left, real_inner_smul_right]
end OperatorDerivativeRewrite.Foundation
