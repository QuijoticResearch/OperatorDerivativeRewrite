import Foundation.FourCubeActualErrorBudget

/-! Actual full32 Haar calibration counterexample to inferring absolute boundary
free-energy error from normalized Gibbs-law error alone. Calibrated weights are
comparison objects, not a redefinition of the standard Wilson action. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.FourCubeScalarCalibration
open QuaternionSU2Representation FourCubeHaarParity FourCubeCompletedHaar
open FourCubeFullHaarGaussianLimit FourCubeActualErrorBudget

def weight (lambda beta : ℝ) (b : Fin 3 → SU2) (U : InteriorState) : ℝ :=
  Real.exp lambda*standardWeight beta b U
def partition (lambda beta : ℝ) (b : Fin 3 → SU2) : ℝ :=
  ∫ U,weight lambda beta b U ∂interiorHaar
def freeEnergy (lambda beta : ℝ) (b : Fin 3 → SU2) : ℝ :=
  -Real.log (partition lambda beta b)

theorem weight_integrable (lambda beta : ℝ) (b : Fin 3 → SU2) :
    Integrable (weight lambda beta b) interiorHaar := (standard_integrable beta b).const_mul _

theorem partition_eq (lambda beta : ℝ) (b : Fin 3 → SU2) :
    partition lambda beta b=Real.exp lambda*standardPartition beta b :=
  integral_const_mul _ _

theorem partition_positive (lambda beta : ℝ) (b : Fin 3 → SU2) :
    0 < partition lambda beta b := by
  rw [partition_eq]
  exact mul_pos (Real.exp_pos _) (standard_positive _ _)

/-- Pointwise equality of the actual normalized full32 Haar densities. -/
theorem normalized_density_eq (lambda beta : ℝ) (b : Fin 3 → SU2) (U : InteriorState) :
    weight lambda beta b U/partition lambda beta b=
      standardWeight beta b U/standardPartition beta b := by
  rw [weight,partition_eq]
  field_simp [Real.exp_ne_zero,(standard_positive beta b).ne']

theorem observable_eq (lambda beta : ℝ) (b : Fin 3 → SU2) (f : InteriorState → ℝ)
    (hf : Integrable (fun U => f U*standardWeight beta b U) interiorHaar) :
    Integrable (fun U => f U*weight lambda beta b U) interiorHaar ∧
      (∫ U,f U*weight lambda beta b U ∂interiorHaar)/partition lambda beta b=
        (∫ U,f U*standardWeight beta b U ∂interiorHaar)/standardPartition beta b := by
  have he : (fun U => f U*weight lambda beta b U)=
      fun U => Real.exp lambda*(f U*standardWeight beta b U) := by
    funext U
    unfold weight
    ring
  constructor
  · rw [he]
    exact hf.const_mul _
  · rw [he,integral_const_mul,partition_eq]
    field_simp [Real.exp_ne_zero,(standard_positive beta b).ne']

theorem free_energy_eq (lambda beta : ℝ) (b : Fin 3 → SU2) :
    freeEnergy lambda beta b=standardFreeEnergy beta b-lambda := by
  rw [freeEnergy,partition_eq,Real.log_mul (Real.exp_ne_zero _) (standard_positive beta b).ne',Real.log_exp]
  unfold standardFreeEnergy
  ring

/-- Explicit counterexample: normalized density equality does not determine free energy. -/
theorem unit_shift_counterexample (beta : ℝ) (b : Fin 3 → SU2) :
    (∀ U,weight 1 beta b U/partition 1 beta b=standardWeight beta b U/standardPartition beta b) ∧
      freeEnergy 1 beta b ≠ standardFreeEnergy beta b := by
  refine ⟨normalized_density_eq 1 beta b,?_⟩
  rw [free_energy_eq]
  linarith

def calibration (x y z t : ℝ) : ℝ :=
  (rayFreeEnergy x y z t-rayFreeEnergy x y z (-t))/2
def balancedFreeEnergy (x y z t : ℝ) : ℝ :=
  freeEnergy (calibration x y z t) (1/t^2) (parameters x y z t)

theorem balanced_value (x y z t : ℝ) :
    balancedFreeEnergy x y z t=(rayFreeEnergy x y z t+rayFreeEnergy x y z (-t))/2 := by
  rw [balancedFreeEnergy,free_energy_eq]
  change rayFreeEnergy x y z t-calibration x y z t=_
  unfold calibration
  ring

theorem balanced_even (x y z t : ℝ) :
    balancedFreeEnergy x y z (-t)=balancedFreeEnergy x y z t := by
  rw [balanced_value,balanced_value,neg_neg,add_comm]

theorem balanced_normalized_density (x y z t : ℝ) (U : InteriorState) :
    weight (calibration x y z t) (1/t^2) (parameters x y z t) U/
      partition (calibration x y z t) (1/t^2) (parameters x y z t)=
      standardWeight (1/t^2) (parameters x y z t) U/
        standardPartition (1/t^2) (parameters x y z t) := normalized_density_eq _ _ _ _

/-- The SAME normalized law can have an exactly even calibrated free energy. -/
theorem balanced_odd_zero (x y z t : ℝ) :
    (balancedFreeEnergy x y z t-balancedFreeEnergy x y z (-t))/(2*t)=0 := by
  rw [balanced_even,sub_self,zero_div]

/-- Scalar error is genuinely order t although the normalized density error is zero. -/
theorem calibration_error_limit (x y z : ℝ) :
    Tendsto (fun t : ℝ => (rayFreeEnergy x y z t-balancedFreeEnergy x y z t)/t)
      (𝓝[≠] 0) (𝓝 (coefficient x y z)) := by
  apply (ray_odd_limit x y z).congr'
  filter_upwards with t
  rw [balanced_value]
  ring

def standardLaw (beta : ℝ) (b : Fin 3 → SU2) : Measure InteriorState :=
  interiorHaar.withDensity (fun U => ENNReal.ofReal (standardWeight beta b U/standardPartition beta b))
def calibratedLaw (lambda beta : ℝ) (b : Fin 3 → SU2) : Measure InteriorState :=
  interiorHaar.withDensity (fun U => ENNReal.ofReal (weight lambda beta b U/partition lambda beta b))

theorem standardLaw_probability (beta : ℝ) (b : Fin 3 → SU2) :
    IsProbabilityMeasure (standardLaw beta b) := by
  constructor
  rw [standardLaw,withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hi := (standard_integrable beta b).div_const (standardPartition beta b)
  have hn (U : InteriorState) : 0 ≤ standardWeight beta b U/standardPartition beta b :=
    div_nonneg (Real.exp_pos _).le (standard_positive beta b).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hn),integral_div]
  change ENNReal.ofReal (standardPartition beta b/standardPartition beta b)=1
  rw [div_self (standard_positive beta b).ne']
  norm_num

theorem calibratedLaw_eq (lambda beta : ℝ) (b : Fin 3 → SU2) :
    calibratedLaw lambda beta b=standardLaw beta b := by
  apply congrArg (fun d : InteriorState → ENNReal => interiorHaar.withDensity d)
  funext U
  rw [normalized_density_eq]

theorem calibratedLaw_probability (lambda beta : ℝ) (b : Fin 3 → SU2) :
    IsProbabilityMeasure (calibratedLaw lambda beta b) := by
  rw [calibratedLaw_eq]
  exact standardLaw_probability beta b

/-- Zero is the actual integral of an identically zero density difference. -/
theorem density_error_zero (lambda beta : ℝ) (b : Fin 3 → SU2) :
    (∫ U,|weight lambda beta b U/partition lambda beta b-
      standardWeight beta b U/standardPartition beta b| ∂interiorHaar)=0 := by
  simp only [normalized_density_eq,sub_self,abs_zero,integral_zero]

/-- No finite constant can control absolute free-energy error by normalized L1 density error. -/
theorem no_free_energy_bound_from_density_error (K beta : ℝ) (b : Fin 3 → SU2) :
    ¬ (|freeEnergy 1 beta b-standardFreeEnergy beta b| ≤
      K*(∫ U,|weight 1 beta b U/partition 1 beta b-
        standardWeight beta b U/standardPartition beta b| ∂interiorHaar)) := by
  rw [density_error_zero,free_energy_eq]
  norm_num

end OperatorDerivativeRewrite.Foundation.FourCubeScalarCalibration
