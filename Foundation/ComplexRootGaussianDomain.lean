import Foundation.PoissonSuperexponentialObstruction
import Foundation.GaussianSchwartzKernel
import Foundation.MarkedRenewalMartingale

/-! Actual complex paths expose integrability limits of an entire Gaussian extension. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal SchwartzMap
namespace OperatorDerivativeRewrite.Foundation.ComplexRootGaussianDomain
open ComplexFourthRootWalk

def gaussian (z : ℂ) : ℂ := Complex.exp (-z^2)

theorem gaussian_continuous : Continuous gaussian := by unfold gaussian; fun_prop

theorem gaussian_differentiable : Differentiable ℂ gaussian := by unfold gaussian; fun_prop

theorem gaussian_real (x : ℝ) : gaussian (x : ℂ) = (GaussianSchwartzKernel.realSchwartz x : ℂ) := by
  change Complex.exp (-(x : ℂ)^2) = (Real.exp (-x^2) : ℂ)
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

def verticalSample (m : ℕ) : Sample (m+m) :=
  Fin.addCases (fun _ : Fin m => 0) (fun _ : Fin m => 1)

theorem vertical_terminal (a : ℝ) (m : ℕ) :
    terminal (m+m) a (verticalSample m) = 2*(m : ℂ)*(a : ℂ)*Complex.I := by
  unfold terminal
  rw [Fin.sum_univ_add]
  have hleft (i : Fin m) : verticalSample m (i.castAdd m) = 0 := by simp [verticalSample]
  have hright (i : Fin m) : verticalSample m (Fin.natAdd m i) = 1 := Fin.addCases_right i
  have hL : (fun i : Fin m => increment (m+m) a (i.castAdd m) (verticalSample m)) =
      (fun _ => ComplexFourthRootNoise.noise a 0) := by
    funext i
    change ComplexFourthRootNoise.noise a (verticalSample m (i.castAdd m)) = _
    rw [hleft]
  have hR : (fun i : Fin m => increment (m+m) a (Fin.natAdd m i) (verticalSample m)) =
      (fun _ => ComplexFourthRootNoise.noise a 1) := by
    funext i
    change ComplexFourthRootNoise.noise a (verticalSample m (Fin.natAdd m i)) = _
    rw [hright]
  rw [hL,hR]
  simp [ComplexFourthRootNoise.noise, ComplexFourthRootNoise.root, nsmul_eq_mul]
  ring

theorem vertical_gaussian_norm (a : ℝ) (m : ℕ) :
    ‖gaussian (terminal (m+m) a (verticalSample m))‖ = Real.exp (4*a^2*(m : ℝ)^2) := by
  rw [vertical_terminal]
  unfold gaussian
  rw [Complex.norm_exp]
  congr 1
  norm_num [pow_two, Complex.mul_re, Complex.mul_im]
  ring

theorem noise_singleton (k : Fin 4) :
    ComplexFourthRootNoise.probability {k} = (1/4 : ℝ≥0∞) := by
  simp [ComplexFourthRootNoise.probability, PMF.uniformOfFintype_apply]

theorem sample_singleton_real (n : ℕ) (ω : Sample n) :
    (probability n).real {ω} = (1/4 : ℝ)^n := by
  simp [Measure.real, probability, Measure.pi_singleton, noise_singleton]

theorem walk_norm_lower (a : ℝ) (m : ℕ) :
    (1/4 : ℝ)^(m+m)*Real.exp (4*a^2*(m : ℝ)^2) ≤
      ∫ ω, ‖gaussian (terminal (m+m) a ω)‖ ∂probability (m+m) := by
  let ω₀ := verticalSample m
  have hA : MeasurableSet ({ω₀} : Set (Sample (m+m))) := measurableSet_singleton _
  have hc : ∀ᵐ ω : Sample (m+m) ∂probability (m+m),
      ({ω₀} : Set (Sample (m+m))).indicator (fun _ => ‖gaussian (terminal (m+m) a ω₀)‖) ω ≤
        ‖gaussian (terminal (m+m) a ω)‖ := by
    filter_upwards with ω
    by_cases h : ω = ω₀
    · subst ω
      simp
    · simp [Set.indicator, h, norm_nonneg]
  have he := integral_mono_ae ((integrable_const _).indicator hA) Integrable.of_finite hc
  rw [integral_indicator_const _ hA] at he
  simpa only [smul_eq_mul, sample_singleton_real, ω₀, vertical_gaussian_norm] using he

theorem walk_norm_transfer (n : ℕ) (a : ℝ) :
    (∫ z, ‖gaussian z‖ ∂ComplexFourthRootWalk.law n a) =
      ∫ ω, ‖gaussian (terminal n a ω)‖ ∂probability n := by
  rw [ComplexFourthRootWalk.law, integral_map (terminal_measurable n a).aemeasurable
    gaussian_continuous.norm.aestronglyMeasurable]

theorem weight_quarter (r : ℝ≥0) (n : ℕ) :
    ComplexRootPoissonLaw.weight r n*(1/4 : ℝ)^n =
      Real.exp (-3*(r : ℝ)/4)*ComplexRootPoissonLaw.weight (r/4) n := by
  have he : Real.exp (-3*(r : ℝ)/4)*Real.exp (-(r : ℝ)/4) = Real.exp (-(r : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold ComplexRootPoissonLaw.weight
  simp only [NNReal.coe_div, NNReal.coe_ofNat, div_pow, one_pow]
  rw [← he]
  ring

theorem not_integrable_compound (r : ℝ≥0) (hr : 0 < r) (a : ℝ) (ha : a ≠ 0) :
    ¬ Integrable gaussian (ComplexRootPoissonLaw.law r a) := by
  intro hi
  rw [ComplexRootPoissonLaw.law_sum] at hi
  have hs := (integrable_sum_measure_iff.mp hi).2
  simp_rw [integral_smul_measure,
    ENNReal.toReal_ofReal (ComplexRootPoissonLaw.weight_nonneg r _),
    smul_eq_mul, walk_norm_transfer] at hs
  have hsEven := hs.comp_injective (show Function.Injective (fun n : ℕ => n+n) from by
    intro i j hij
    dsimp only at hij
    omega)
  let C := Real.exp (-3*(r : ℝ)/4)
  have hC : C ≠ 0 := Real.exp_ne_zero _
  have hlow (m : ℕ) : C*PoissonSuperexponentialObstruction.term (r/4) (a^2) (m+m) ≤
      ComplexRootPoissonLaw.weight r (m+m)*
        (∫ ω, ‖gaussian (terminal (m+m) a ω)‖ ∂probability (m+m)) := by
    have he : a^2*((m+m : ℕ) : ℝ)^2 = 4*a^2*(m : ℝ)^2 := by push_cast; ring
    calc
      _ = (ComplexRootPoissonLaw.weight r (m+m)*(1/4 : ℝ)^(m+m)) *
          Real.exp (4*a^2*(m : ℝ)^2) := by
        unfold C PoissonSuperexponentialObstruction.term
        rw [← mul_assoc, ← weight_quarter, he]
      _ ≤ _ := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (walk_norm_lower a m)
          (ComplexRootPoissonLaw.weight_nonneg r (m+m))
  have hbound : Summable (fun m : ℕ =>
      C*PoissonSuperexponentialObstruction.term (r/4) (a^2) (m+m)) :=
    hsEven.of_nonneg_of_le (fun m => mul_nonneg (Real.exp_nonneg _)
      (PoissonSuperexponentialObstruction.term_nonneg _ _ _)) hlow
  have hsum := hbound.mul_left C⁻¹
  have hbad := PoissonSuperexponentialObstruction.not_summable_subsequence
    (r/4) (by positivity) (a^2) (sq_pos_of_ne_zero ha) (fun m : ℕ => m+m)
    (by
      refine tendsto_atTop_mono (fun m : ℕ => ?_) tendsto_id
      change m ≤ m+m
      omega)
  apply hbad
  simpa only [← mul_assoc, inv_mul_cancel₀ hC, one_mul] using hsum

theorem not_integrable_process (t : ℝ≥0) (ht : 0 < t) (a : ℝ) (ha : a ≠ 0) :
    ¬ Integrable (fun ω : MarkedRootRenewalProcess.StateSample =>
      gaussian (MarkedRenewalMartingale.process a t ω)) MarkedRootRenewalProcess.probability := by
  intro hi
  apply not_integrable_compound t ht a ha
  have hm := (integrable_map_measure gaussian_continuous.aestronglyMeasurable
    (MarkedRenewalMartingale.process_measurable a t).aemeasurable).mpr hi
  rw [MarkedRenewalMartingale.process_law] at hm
  exact hm

end OperatorDerivativeRewrite.Foundation.ComplexRootGaussianDomain
