import Foundation.MeasurableExponentialKernel
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Disintegration.Basic

/-! Disintegration of an actual globally normalized exponential density. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.ExponentialJointDisintegration
open MeasurableExponentialKernel
variable {P E : Type*} [MeasurableSpace P] [MeasurableSpace E]
variable (ρ : Measure P) (μ : Measure E) [IsProbabilityMeasure ρ] [IsProbabilityMeasure μ]
variable (X : P → E → ℝ)

def totalPartition : ℝ := ∫ z, Real.exp (X z.1 z.2) ∂ρ.prod μ

def joint : Measure (P × E) := (ρ.prod μ).withDensity (fun z =>
  ENNReal.ofReal (Real.exp (X z.1 z.2) / totalPartition ρ μ X))

def boundaryDensity (p : P) : ℝ := partition μ X p / totalPartition ρ μ X

def boundary : Measure P := ρ.withDensity (fun p => ENNReal.ofReal (boundaryDensity ρ μ X p))

theorem total_positive (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ)) :
    0 < totalPartition ρ μ X :=
  partition_positive (ρ.prod μ) (fun (_ : Unit) (z : P × E) => X z.1 z.2) () hJ

omit [IsProbabilityMeasure ρ] in
theorem boundaryDensity_measurable (hX : Measurable (Function.uncurry X)) :
    Measurable (boundaryDensity ρ μ X) :=
  (partition_measurable μ X hX).div_const _

theorem boundary_probability (_hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ)
    (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ)) :
    IsProbabilityMeasure (boundary ρ μ X) := by
  have hi : Integrable (boundaryDensity ρ μ X) ρ := hJ.integral_prod_left.div_const _
  have hn : ∀ p, 0 ≤ boundaryDensity ρ μ X p := fun p =>
    (div_pos (partition_positive μ X p (hI p)) (total_positive ρ μ X hJ)).le
  have he : (∫ p, boundaryDensity ρ μ X p ∂ρ) = 1 := by
    change (∫ p, partition μ X p / totalPartition ρ μ X ∂ρ) = 1
    rw [integral_div]
    have hz : (∫ p, partition μ X p ∂ρ) = totalPartition ρ μ X :=
      (integral_prod _ hJ).symm
    rw [hz]
    exact div_self (total_positive ρ μ X hJ).ne'
  constructor
  rw [boundary, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn), he]
  norm_num

theorem factorization (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ) :
    joint ρ μ X = (boundary ρ μ X) ⊗ₘ (kernel μ X) := by
  let _ : IsMarkovKernel ((Kernel.const P μ).withDensity
      (fun p x => ENNReal.ofReal (density μ X p x))) := kernel_markov μ X hX hI
  rw [boundary, kernel, Measure.withDensity_compProd_withDensity
    (boundaryDensity_measurable ρ μ X hX).ennreal_ofReal
    (density_measurable μ X hX).ennreal_ofReal, Measure.compProd_const]
  unfold joint
  apply withDensity_congr_ae
  filter_upwards with z
  rw [← ENNReal.ofReal_mul (by
    dsimp only [boundaryDensity]
    exact div_nonneg (partition_positive μ X z.1 (hI z.1)).le
      (integral_nonneg fun _ => (Real.exp_pos _).le))]
  congr 1
  dsimp only [boundaryDensity, density]
  by_cases hc : totalPartition ρ μ X = 0
  · simp [hc]
  · field_simp [hc, ne_of_gt (partition_positive μ X z.1 (hI z.1))]

theorem joint_probability (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ)
    (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ)) :
    IsProbabilityMeasure (joint ρ μ X) := by
  let _ := boundary_probability ρ μ X hX hI hJ
  let _ := kernel_markov μ X hX hI
  rw [factorization ρ μ X hX hI]
  infer_instance

theorem boundary_marginal (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ)
    (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ)) :
    (joint ρ μ X).fst = boundary ρ μ X := by
  let _ := boundary_probability ρ μ X hX hI hJ
  let _ := kernel_markov μ X hX hI
  rw [factorization ρ μ X hX hI, Measure.fst_compProd]

theorem conditional_rectangles (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ)
    (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ))
    (s : Set P) (t : Set E) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    joint ρ μ X (s ×ˢ t) = ∫⁻ p in s, kernel μ X p t ∂boundary ρ μ X := by
  let _ := boundary_probability ρ μ X hX hI hJ
  let _ := kernel_markov μ X hX hI
  rw [factorization ρ μ X hX hI, Measure.compProd_apply_prod hs ht]

theorem conditional_kernel (hX : Measurable (Function.uncurry X))
    (hI : ∀ p, Integrable (fun x => Real.exp (X p x)) μ)
    (hJ : Integrable (fun z : P × E => Real.exp (X z.1 z.2)) (ρ.prod μ)) :
    (joint ρ μ X).IsCondKernel (kernel μ X) := by
  constructor
  rw [boundary_marginal ρ μ X hX hI hJ]
  exact (factorization ρ μ X hX hI).symm

end OperatorDerivativeRewrite.Foundation.ExponentialJointDisintegration
