import Foundation.EvenEntireGaussianBudget
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Compact-uniform Gaussian integration using the existing Banach space C(K,C).
Uniform small-quadratic growth supplies a common majorant on compact spatial
sets. Genuine Bochner integrals in C(K,C) and continuous evaluation identify the
actual scalar Gaussian integrals and prove their local-uniform convergence. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianCompactHeat
open EvenEntireGaussianBudget

def compactShift (K : Set ℂ) (F : ℂ → ℂ) (hF : Continuous F) (c : ℂ) (y : ℝ) : C(K,ℂ) :=
  ⟨fun z => F ((z:ℂ)+c*(y:ℂ)),hF.comp (continuous_subtype_val.add continuous_const)⟩

theorem compactShift_continuous (K : Set ℂ)
    (F : ℂ → ℂ) (hF : Continuous F) (c : ℂ) : Continuous (compactShift K F hF c) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℝ × K => F ((p.2:ℂ)+c*(p.1:ℂ)))
  exact hF.comp ((continuous_subtype_val.comp continuous_snd).add
    (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)))

theorem compactShift_limit (K : Set ℂ)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (hF : ∀ n,Continuous (F n)) (hf : Continuous f)
    (hlim : TendstoLocallyUniformly F f atTop) (c : ℂ) (y : ℝ) :
    Tendsto (fun n => compactShift K (F n) (hF n) c y) atTop
      (𝓝 (compactShift K f hf c y)) := by
  apply ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mpr
  intro T hT
  let g : K → ℂ := fun z => (z:ℂ)+c*(y:ℂ)
  have hg : Continuous g := continuous_subtype_val.add continuous_const
  have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hlim) (g '' T) (hT.image hg)
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn
  intro z hz
  exact hn (g z) (mem_image_of_mem g hz)

theorem exists_closedBall_gaussian_majorant (μ : Measure ℝ) [IsGaussian μ]
    (F : ℕ → ℂ → ℂ)
    (hbudget : ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ w : ℂ,
      ‖F n w‖ ≤ C*Real.exp (ε*‖w‖^2)) (M : ℝ) (c : ℂ) :
    ∃ g : ℝ → ℝ,Integrable g μ ∧ (∀ y : ℝ,0 ≤ g y) ∧
      ∀ n : ℕ,∀ z : ℂ,‖z‖ ≤ M → ∀ y : ℝ,‖F n (z+c*(y:ℂ))‖ ≤ g y := by
  obtain ⟨a,ha,hgauss⟩ := IsGaussian.exists_integrable_exp_sq μ
  let ε : ℝ := a/(4*(‖c‖^2+1))
  have hε : 0<ε := div_pos ha (by positivity)
  obtain ⟨C,hC,hbound⟩ := hbudget ε hε
  let g : ℝ → ℝ := fun y => C*Real.exp (2*ε*M^2)*Real.exp (a*‖y‖^2)
  have hg : Integrable g μ := hgauss.const_mul (C*Real.exp (2*ε*M^2))
  have hcoef : 2*ε*‖c‖^2 ≤ a := by
    have he : ε*(4*(‖c‖^2+1))=a := by dsimp [ε]; field_simp
    nlinarith [mul_nonneg hε.le (sq_nonneg ‖c‖)]
  refine ⟨g,hg,fun y => by dsimp [g]; positivity,?_⟩
  intro n z hz y
  have hs := mul_le_mul_of_nonneg_left (shifted_norm_square z c y) hε.le
  have hc := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)
  have hsq := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg z) hz 2) (by positivity : 0 ≤ 2*ε)
  calc
    _ ≤ C*Real.exp (ε*‖z+c*(y:ℂ)‖^2) := hbound n _
    _ ≤ C*Real.exp (2*ε*M^2+a*‖y‖^2) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hC.le
    _ = g y := by dsimp [g]; rw [Real.exp_add]; ring

theorem gaussian_integral_uniform_on_compact (μ : Measure ℝ) [IsGaussian μ]
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (hF : ∀ n,Continuous (F n)) (hf : Continuous f)
    (hlim : TendstoLocallyUniformly F f atTop)
    (hbudget : ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ w : ℂ,
      ‖F n w‖ ≤ C*Real.exp (ε*‖w‖^2)) (c : ℂ) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n z => ∫ y : ℝ,F n (z+c*(y:ℂ)) ∂μ)
      (fun z => ∫ y : ℝ,f (z+c*(y:ℂ)) ∂μ) atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨M,hM,hsub⟩ := hK.isBounded.subset_closedBall_lt 0 (0:ℂ)
  obtain ⟨g,hg,hg0,hbound⟩ := exists_closedBall_gaussian_majorant μ F hbudget M c
  let FH : ℕ → ℝ → C(K,ℂ) := fun n => compactShift K (F n) (hF n) c
  let GH : ℝ → C(K,ℂ) := compactShift K f hf c
  have hpt (y : ℝ) : Tendsto (fun n => FH n y) atTop (𝓝 (GH y)) :=
    compactShift_limit K F f hF hf hlim c y
  have hn (n : ℕ) (y : ℝ) : ‖FH n y‖ ≤ g y := by
    apply (ContinuousMap.norm_le _ (hg0 y)).mpr
    intro z
    exact hbound n (z:ℂ) (mem_closedBall_zero_iff.mp (hsub z.property)) y
  have hFn (n : ℕ) : Continuous (FH n) := compactShift_continuous K (F n) (hF n) c
  have hGn : Continuous GH := compactShift_continuous K f hf c
  have hFi (n : ℕ) : Integrable (FH n) μ :=
    hg.mono' (hFn n).aestronglyMeasurable (Filter.Eventually.of_forall (hn n))
  have hGnBound (y : ℝ) : ‖GH y‖ ≤ g y :=
    le_of_tendsto ((continuous_norm.continuousAt.tendsto).comp (hpt y))
      (Filter.Eventually.of_forall (fun n => hn n y))
  have hGi : Integrable GH μ :=
    hg.mono' hGn.aestronglyMeasurable (Filter.Eventually.of_forall hGnBound)
  have ht := tendsto_integral_of_dominated_convergence g
    (fun n => (hFn n).aestronglyMeasurable) hg
    (fun n => Filter.Eventually.of_forall (hn n)) (Filter.Eventually.of_forall hpt)
  have hu := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp ht)
    univ isCompact_univ
  have hEvalF (n : ℕ) (z : K) : (∫ y : ℝ,FH n y ∂μ) z=
      ∫ y : ℝ,F n ((z:ℂ)+c*(y:ℂ)) ∂μ :=
    ((ContinuousMap.evalCLM ℂ z).integral_comp_comm (hFi n)).symm
  have hEvalG (z : K) : (∫ y : ℝ,GH y ∂μ) z=
      ∫ y : ℝ,f ((z:ℂ)+c*(y:ℂ)) ∂μ :=
    ((ContinuousMap.evalCLM ℂ z).integral_comp_comm hGi).symm
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with n hn
  intro z hz
  have hh := hn ⟨z,hz⟩ (mem_univ _)
  rw [hEvalF,hEvalG] at hh
  exact hh

theorem gaussian_integral_locally_uniform (μ : Measure ℝ) [IsGaussian μ]
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (hF : ∀ n,Continuous (F n)) (hf : Continuous f)
    (hlim : TendstoLocallyUniformly F f atTop)
    (hbudget : ∀ ε : ℝ,0<ε → ∃ C : ℝ,0<C ∧ ∀ n : ℕ,∀ w : ℂ,
      ‖F n w‖ ≤ C*Real.exp (ε*‖w‖^2)) (c : ℂ) :
    TendstoLocallyUniformly (fun n z => ∫ y : ℝ,F n (z+c*(y:ℂ)) ∂μ)
      (fun z => ∫ y : ℝ,f (z+c*(y:ℂ)) ∂μ) atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  exact gaussian_integral_uniform_on_compact μ F f hF hf hlim hbudget c K hK


end OperatorDerivativeRewrite.Foundation.GaussianCompactHeat

