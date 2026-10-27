import Foundation.PhysicalHeatTransitionLimit
import Mathlib.Order.Interval.Finset.Basic

/-!
# Finite Fourier boxes and physical heat probability laws

Uniform Fourier boxes in `ℤ³` have `(2n+1)^3` frequencies. Their normalized
trigonometric squares are probability densities. The coefficient at a fixed
frequency is the normalized overlap of a box with its translate; an inner-box
bound proves that this coefficient tends to one. Combined with the compactness
reduction in `PhysicalHeatTransitionLimit`, this constructs an actual
probability measure for every covariance-symbol heat multiplier with zero
constant-mode rate. Measure uniqueness, convolution composition, a Markov
kernel and a process with paths are not asserted here.
-/

open OperatorDerivativeRewrite.Foundation
open FiniteFourierDifferentialTrace
open Filter MeasureTheory AddCircle
open scoped NNReal ComplexConjugate Topology

noncomputable section

namespace OperatorDerivativeRewrite.Foundation.PhysicalHeatFiniteBox

def cube (n : ℕ) : Finset Wave :=
  (Finset.univ.pi (fun _ : Fin 3 => Finset.Icc (-(n : ℤ)) (n : ℤ))).image
    (fun g j => g j (Finset.mem_univ j))

theorem mem_cube (n : ℕ) (k : Wave) :
    k ∈ cube n ↔ ∀ j : Fin 3, -(n : ℤ) ≤ k j ∧ k j ≤ (n : ℤ) := by
  constructor
  · intro hk j
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_Icc.mp (Finset.mem_pi.mp hg j (Finset.mem_univ j))
  · intro hk
    apply Finset.mem_image.mpr
    refine ⟨(fun j _ => k j), ?_, rfl⟩
    apply Finset.mem_pi.mpr
    intro j hj
    exact Finset.mem_Icc.mpr (hk j)

theorem card_cube (n : ℕ) : (cube n).card = (2*n+1)^3 := by
  have hinj : Function.Injective
      (fun g : (j : Fin 3) → j ∈ (Finset.univ : Finset (Fin 3)) → ℤ =>
        fun j => g j (Finset.mem_univ j)) := by
    intro g h he
    funext j hj
    exact congrFun he j
  rw [cube, Finset.card_image_of_injective _ hinj, Finset.card_pi]
  have hcard : (Finset.Icc (-(n : ℤ)) (n : ℤ)).card = 2*n+1 := by
    rw [Int.card_Icc]
    omega
  simp [hcard, Finset.prod_const]

def cubePolynomial (n : ℕ) : Fourier :=
  ∑ k ∈ cube n, AddMonoidAlgebra.single k (1 : ℂ)

theorem cubePolynomial_coeff (n : ℕ) (k : Wave) :
    (cubePolynomial n).coeff k = if k ∈ cube n then 1 else 0 := by
  classical
  simp [cubePolynomial, AddMonoidAlgebra.coeff_sum,
    Finsupp.single_apply]

theorem cubePolynomial_reflection (n : ℕ) :
    FiniteFourierReality.reflection (cubePolynomial n) =
      ∑ k ∈ cube n, AddMonoidAlgebra.single (-k) (1 : ℂ) := by
  simp [cubePolynomial, map_sum, FiniteFourierReality.reflection_single]

theorem cubePolynomial_square_coeff (n : ℕ) (k : Wave) :
    (FiniteFourierReality.reflection (cubePolynomial n) *
      cubePolynomial n).coeff k =
      ((cube n).filter (fun j => j + k ∈ cube n)).card := by
  classical
  rw [cubePolynomial_reflection, cubePolynomial]
  simp only [Finset.sum_mul, Finset.mul_sum, AddMonoidAlgebra.coeff_sum]
  rw [Finset.sum_comm]
  simp [AddMonoidAlgebra.single_mul_single, Finsupp.single_apply]
  have hpred (x y : Wave) : -x + y = k ↔ y = x + k := by
    constructor
    · intro h
      calc y = x + (-x + y) := by abel
        _ = x + k := by rw [h]
    · intro h
      rw [h]
      abel
  simp_rw [hpred]
  simp only [Finset.filter_eq', apply_ite, Finset.card_singleton,
    Finset.card_empty, Nat.cast_one, Nat.cast_zero,
    Finset.card_filter]
  simp

theorem cubePolynomial_energy (n : ℕ) :
    (∑ k ∈ (cubePolynomial n).coeff.support,
      conj ((cubePolynomial n).coeff k) * (cubePolynomial n).coeff k) =
      (cube n).card := by
  rw [← PhysicalHeatMarkovOrder.square_coeff_zero_energy,
    cubePolynomial_square_coeff]
  simp

theorem square_real_smul_coeff (a : ℝ) (f : Fourier) (k : Wave) :
    (FiniteFourierReality.reflection (a • f) * (a • f)).coeff k =
      ((a*a : ℝ) : ℂ) * (FiniteFourierReality.reflection f * f).coeff k := by
  rw [map_smul]
  simp [mul_assoc]

def normalizedCube (n : ℕ) : Fourier :=
  (Real.sqrt ((cube n).card : ℝ))⁻¹ • cubePolynomial n

theorem normalizedCube_square_coeff (n : ℕ) (k : Wave) :
    (FiniteFourierReality.reflection (normalizedCube n) *
      normalizedCube n).coeff k =
      (((Real.sqrt ((cube n).card : ℝ))⁻¹)^2 : ℂ) *
        (((cube n).filter (fun j => j + k ∈ cube n)).card : ℂ) := by
  rw [normalizedCube, square_real_smul_coeff, cubePolynomial_square_coeff]
  simp [pow_two]

theorem normalizedCube_energy (n : ℕ) :
    (∑ k ∈ (normalizedCube n).coeff.support,
      conj ((normalizedCube n).coeff k) * (normalizedCube n).coeff k) = 1 := by
  rw [← PhysicalHeatMarkovOrder.square_coeff_zero_energy,
    normalizedCube_square_coeff]
  have hfilter : (cube n).filter (fun j => j + 0 ∈ cube n) = cube n := by simp
  rw [hfilter]
  have hcard : 0 < ((cube n).card : ℝ) := by
    rw [card_cube]
    positivity
  have hs : (Real.sqrt ((cube n).card : ℝ))^2 = ((cube n).card : ℝ) :=
    Real.sq_sqrt hcard.le
  have hnz : Real.sqrt ((cube n).card : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hcard)
  have hreal : ((Real.sqrt ((cube n).card : ℝ))⁻¹)^2 *
      ((cube n).card : ℝ) = 1 := by
    calc
      ((Real.sqrt ((cube n).card : ℝ))⁻¹)^2 * ((cube n).card : ℝ) =
          ((Real.sqrt ((cube n).card : ℝ))⁻¹)^2 *
            (Real.sqrt ((cube n).card : ℝ))^2 := by rw [hs]
      _ = 1 := by field_simp [hnz]
  exact_mod_cast hreal

theorem real_lower_ratio_tendsto (m : ℕ) :
    Tendsto (fun n : ℕ =>
      (1 - (2*(m:ℝ))/(2*(n:ℝ)+1))^3) atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => 2*(n:ℝ)) atTop atTop :=
    hbase.const_mul_atTop (by norm_num)
  have hden : Tendsto (fun n : ℕ => 2*(n:ℝ)+1) atTop atTop :=
    hmul.atTop_add tendsto_const_nhds
  have hfrac : Tendsto (fun n : ℕ => (2*(m:ℝ))/(2*(n:ℝ)+1))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using (hone.sub hfrac).pow 3

theorem lower_cube_ratio_tendsto (m : ℕ) :
    Tendsto (fun n : ℕ =>
      (((2*(n-m)+1)^3 : ℕ) : ℝ) / (((2*n+1)^3 : ℕ) : ℝ))
      atTop (𝓝 1) := by
  have heq : ∀ᶠ n : ℕ in atTop,
      (((2*(n-m)+1)^3 : ℕ) : ℝ) / (((2*n+1)^3 : ℕ) : ℝ) =
        (1 - (2*(m:ℝ))/(2*(n:ℝ)+1))^3 := by
    filter_upwards [eventually_ge_atTop m] with n hn
    have hnreal : ((n-m:ℕ):ℝ) = (n:ℝ)-(m:ℝ) := by
      simp [Nat.cast_sub hn]
    have hden : 2*(n:ℝ)+1 ≠ 0 := by positivity
    push_cast [hnreal, div_pow]
    field_simp
    ring
  exact (real_lower_ratio_tendsto m).congr' (heq.mono (fun _ h => h.symm))

def radius (k : Wave) : ℕ :=
  max (k 0).natAbs (max (k 1).natAbs (k 2).natAbs)

theorem radius_bounds (k : Wave) (j : Fin 3) :
    -(radius k : ℤ) ≤ k j ∧ k j ≤ (radius k : ℤ) := by
  have hnat : (k j).natAbs ≤ radius k := by
    fin_cases j <;> simp [radius]
  have hcast : ((k j).natAbs : ℤ) ≤ (radius k : ℤ) := by
    exact_mod_cast hnat
  rw [Nat.cast_natAbs] at hcast
  exact abs_le.mp hcast

theorem cube_translate_inner (k : Wave) (n : ℕ)
    (hn : radius k ≤ n) :
    cube (n - radius k) ⊆
      (cube n).filter (fun j => j + k ∈ cube n) := by
  intro j hj
  rw [Finset.mem_filter]
  have hsmall := (mem_cube (n-radius k) j).mp hj
  constructor
  · apply (mem_cube n j).mpr
    intro q
    have hq := hsmall q
    omega
  · apply (mem_cube n (j+k)).mpr
    intro q
    have hq := hsmall q
    have hk := radius_bounds k q
    constructor <;> simp only [Pi.add_apply] <;> omega

theorem overlap_ratio_tendsto (k : Wave) :
    Tendsto (fun n : ℕ =>
      (((cube n).filter (fun j => j + k ∈ cube n)).card : ℝ) /
        ((cube n).card : ℝ)) atTop (𝓝 1) := by
  have hlow : ∀ᶠ n : ℕ in atTop,
      (((2*(n-radius k)+1)^3 : ℕ) : ℝ) / (((2*n+1)^3 : ℕ) : ℝ) ≤
        (((cube n).filter (fun j => j + k ∈ cube n)).card : ℝ) /
          ((cube n).card : ℝ) := by
    filter_upwards [eventually_ge_atTop (radius k)] with n hn
    have hsub := cube_translate_inner k n hn
    have hcard := Finset.card_le_card hsub
    rw [card_cube (n-radius k)] at hcard
    have hcast : (((2*(n-radius k)+1)^3 : ℕ) : ℝ) ≤
        (((cube n).filter (fun j => j + k ∈ cube n)).card : ℝ) := by
      exact_mod_cast hcard
    rw [card_cube n]
    exact div_le_div_of_nonneg_right hcast (by positivity)
  have hhigh : ∀ᶠ n : ℕ in atTop,
      (((cube n).filter (fun j => j + k ∈ cube n)).card : ℝ) /
        ((cube n).card : ℝ) ≤ 1 := by
    filter_upwards [] with n
    have hcard := Finset.card_le_card (Finset.filter_subset (fun j => j + k ∈ cube n) (cube n))
    have hcast : (((cube n).filter (fun j => j + k ∈ cube n)).card : ℝ) ≤
        ((cube n).card : ℝ) := by exact_mod_cast hcard
    have hden : 0 < ((cube n).card : ℝ) := by rw [card_cube]; positivity
    exact (div_le_one hden).mpr hcast
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (lower_cube_ratio_tendsto (radius k)) tendsto_const_nhds hlow hhigh

theorem normalizedCube_coeff_ratio (n : ℕ) (k : Wave) :
    (FiniteFourierReality.reflection (normalizedCube n) *
      normalizedCube n).coeff k =
      (((((cube n).filter (fun j => j + k ∈ cube n)).card : ℝ) /
        ((cube n).card : ℝ) : ℝ) : ℂ) := by
  rw [normalizedCube_square_coeff]
  have hcard : 0 ≤ ((cube n).card : ℝ) := by positivity
  have hs : (Real.sqrt ((cube n).card : ℝ))^2 = ((cube n).card : ℝ) :=
    Real.sq_sqrt hcard
  norm_cast
  rw [inv_pow, hs]
  simp [div_eq_mul_inv, mul_comm]

theorem normalizedCube_coeff_tendsto (k : Wave) :
    Tendsto (fun n : ℕ =>
      (FiniteFourierReality.reflection (normalizedCube n) *
        normalizedCube n).coeff k) atTop (𝓝 1) := by
  have h := (overlap_ratio_tendsto k).ofReal
  simpa only [normalizedCube_coeff_ratio, Complex.ofReal_one] using h

theorem exists_physical_heat_law (r : Wave → ℝ≥0)
    (hr : FourierCovarianceCriterion.CovarianceSymbol (fun k => (r k : ℝ)))
    (hr0 : r 0 = 0) (t : ℝ≥0) :
    ∃ μ : MeasureTheory.ProbabilityMeasure (UnitAddTorus (Fin 3)),
      ∀ k : Wave,
        (∫ x : UnitAddTorus (Fin 3), UnitAddTorus.mFourier (-k) x
          ∂(μ : MeasureTheory.Measure (UnitAddTorus (Fin 3)))) =
            (Real.exp (-((t : ℝ) * (r k : ℝ))) : ℂ) := by
  exact PhysicalHeatTransitionLimit.exists_transition_of_approximate_squares
    r hr hr0 t normalizedCube normalizedCube_energy normalizedCube_coeff_tendsto

end OperatorDerivativeRewrite.Foundation.PhysicalHeatFiniteBox
