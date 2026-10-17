import Foundation.HigherHeatRefinement

/-! Actual finite signed heat configurations and their spectral cylinder integrals. -/
noncomputable section
open MeasureTheory Filter FourierTransform
open scoped NNReal Topology SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.HigherHeatCylinderFourier
open GaussianSchwartzKernel HigherHeatSignedLaws

def phase (ξ x : ℝ) : ℂ := Real.fourierChar (-(x*ξ))

theorem phase_norm (ξ x : ℝ) : ‖phase ξ x‖=1 := by simp [phase]

theorem phase_continuous (ξ : ℝ) : Continuous (phase ξ) := by
  unfold phase
  fun_prop

theorem kernel_phase_integrable (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ) :
    Integrable (fun x : ℝ => phase ξ x * (realKernel m hm t ht x : ℂ)) := by
  have hi := evenKernel_integrable m hm t ht
  apply hi.norm.mono' (by unfold phase; fun_prop)
  filter_upwards with x
  rw [norm_mul,phase_norm,one_mul,realKernel_coe]

theorem kernel_fourier (m : ℕ) (hm : 0 < m) (t : ℝ≥0) (ht : 0 < t) (ξ : ℝ) :
    (∫ x : ℝ, phase ξ x * (realKernel m hm t ht x : ℂ)) = HigherHeatL2.symbol m t ξ := by
  have h := congrArg (fun f : 𝓢(ℝ,ℂ) => f ξ) (evenKernel_fourier m hm t ht)
  rw [SchwartzMap.fourier_coe,Real.fourier_eq,evenSymbol_apply] at h
  simp only [phase,realKernel_coe]
  convert h using 1 <;> simp [Circle.smul_def,smul_eq_mul,RCLike.inner_apply,mul_comm]

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def linearImage (B : κ → ι → ℝ) (x : ι → ℝ) (i : κ) : ℝ := ∑ j, B i j*x j

theorem linearImage_measurable (B : κ → ι → ℝ) : Measurable (linearImage B) := by
  apply Measurable.of_eval
  intro i
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.mul (measurable_pi_apply j)

def configurationLaw (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j)
    (B : κ → ι → ℝ) : SignedMeasure (κ → ℝ) :=
  (incrementLaw m hm t ht).map (linearImage B)

theorem configurationLaw_mass (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0)
    (ht : ∀ j, 0 < t j) (B : κ → ι → ℝ) : configurationLaw m hm t ht B Set.univ=1 := by
  rw [configurationLaw,VectorMeasure.map_apply _ (linearImage_measurable B) MeasurableSet.univ,
    Set.preimage_univ,incrementLaw_mass]

def dualImage (B : κ → ι → ℝ) (ξ : κ → ℝ) (j : ι) : ℝ := ∑ i, ξ i*B i j

theorem dot_linearImage (B : κ → ι → ℝ) (ξ : κ → ℝ) (x : ι → ℝ) :
    (∑ i, ξ i*linearImage B x i) = ∑ j, x j*dualImage B ξ j := by
  simp only [linearImage,dualImage,Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext j
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem character_sum (s : Finset ι) (f : ι → ℝ) :
    (Real.fourierChar (∑ j ∈ s, f j) : ℂ) = ∏ j ∈ s, (Real.fourierChar (f j) : ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih => simp [hj,AddChar.map_add_eq_mul,ih]

def cylinderIntegrand (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j)
    (B : κ → ι → ℝ) (ξ : κ → ℝ) (x : ι → ℝ) : ℂ :=
  (Real.fourierChar (-(∑ i, ξ i*linearImage B x i)) : ℂ)*
    (incrementDensity m hm t ht x : ℂ)

theorem cylinderIntegrand_factor (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j)
    (B : κ → ι → ℝ) (ξ : κ → ℝ) (x : ι → ℝ) :
    cylinderIntegrand m hm t ht B ξ x =
      ∏ j, phase (dualImage B ξ j) (x j) * (realKernel m hm (t j) (ht j) (x j) : ℂ) := by
  unfold cylinderIntegrand
  rw [dot_linearImage,← Finset.sum_neg_distrib,character_sum]
  simp only [phase,incrementDensity,Complex.ofReal_prod,Finset.prod_mul_distrib]

theorem cylinderIntegrand_integrable (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j)
    (B : κ → ι → ℝ) (ξ : κ → ℝ) :
    Integrable (cylinderIntegrand m hm t ht B ξ) (Measure.pi (fun _ : ι => volume)) := by
  have h := Integrable.fintype_prod (fun j => kernel_phase_integrable m hm (t j) (ht j) (dualImage B ξ j))
  simpa only [← cylinderIntegrand_factor] using h

def cylinderFourier (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j)
    (B : κ → ι → ℝ) (ξ : κ → ℝ) : ℂ :=
  ∫ x : ι → ℝ, cylinderIntegrand m hm t ht B ξ x ∂Measure.pi (fun _ : ι => volume)

theorem cylinderFourier_eq (m : ℕ) (hm : 0 < m) (t : ι → ℝ≥0) (ht : ∀ j, 0 < t j)
    (B : κ → ι → ℝ) (ξ : κ → ℝ) :
    cylinderFourier m hm t ht B ξ = ∏ j, HigherHeatL2.symbol m (t j) (dualImage B ξ j) := by
  unfold cylinderFourier
  simp_rw [cylinderIntegrand_factor]
  rw [integral_fintype_prod_eq_prod (fun j (x : ℝ) =>
    phase (dualImage B ξ j) x * (realKernel m hm (t j) (ht j) x : ℂ))]
  apply Finset.prod_congr rfl
  intro j _
  exact kernel_fourier m hm (t j) (ht j) (dualImage B ξ j)

def cumulativeMatrix (n : ℕ) (i j : Fin n) : ℝ := if j ≤ i then 1 else 0

def positionLaw (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ j, 0 < t j) :
    SignedMeasure (Fin n → ℝ) := configurationLaw m hm t ht (cumulativeMatrix n)

theorem cumulative_apply (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    linearImage (cumulativeMatrix n) x i = ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), x j := by
  classical
  simp [linearImage,cumulativeMatrix,Finset.sum_filter]

theorem cumulative_dual (n : ℕ) (ξ : Fin n → ℝ) (j : Fin n) :
    dualImage (cumulativeMatrix n) ξ j = ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), ξ i := by
  classical
  simp [dualImage,cumulativeMatrix,Finset.sum_filter]

theorem positionLaw_mass (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ j, 0 < t j) :
    positionLaw n m hm t ht Set.univ=1 := configurationLaw_mass m hm t ht _

theorem positionFourier_eq (n m : ℕ) (hm : 0 < m) (t : Fin n → ℝ≥0) (ht : ∀ j, 0 < t j)
    (ξ : Fin n → ℝ) :
    cylinderFourier m hm t ht (cumulativeMatrix n) ξ =
      ∏ j, HigherHeatL2.symbol m (t j) (∑ i ∈ Finset.univ.filter (fun i => j ≤ i), ξ i) := by
  rw [cylinderFourier_eq]
  simp_rw [cumulative_dual]

end OperatorDerivativeRewrite.Foundation.HigherHeatCylinderFourier
