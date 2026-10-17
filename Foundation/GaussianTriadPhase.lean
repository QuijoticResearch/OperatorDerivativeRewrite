import Foundation.ParameterizedTriadRepresentative
import Foundation.GaussianCore
import Mathlib.MeasureTheory.Function.L2Space

/-! An actual Gaussian random phase has zero mean angular-transfer rate and nonzero fluctuations. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Polynomial
open scoped ENNReal
namespace OperatorDerivativeRewrite.Foundation.GaussianTriadPhase
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
abbrev γ := GaussianCore.γ
private instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
private instance : NullSingletonClass γ := nullSingletonClass_gaussianReal (by norm_num)

def phaseRate (c : ℝ) : ℝ := SectorTransferSymmetry.rate SectorTriadSign.modes
  AngularTriadPartition.sector (ParameterizedSectorTriad.polarization 2 1 c)
def phaseDen (c : ℝ) : ℝ := 30*c^4-5*c^2+247/8

theorem phase_energy_pos (c : ℝ) : 0 < ParameterizedSectorTriad.energyValue 2 1 c := by
  unfold ParameterizedSectorTriad.energyValue
  nlinarith [sq_nonneg c]

theorem phaseRate_formula (c : ℝ) : phaseRate c= -48*c/phaseDen c := by
  rw [phaseRate,ParameterizedSectorTriad.rate_exact 2 1 c (phase_energy_pos c)]
  unfold ParameterizedSectorTriad.imbalance ParameterizedSectorTriad.denominator
    ParameterizedSectorTriad.fourthValue ParameterizedSectorTriad.energyValue phaseDen
  norm_num
  ring

theorem phaseDen_square (c : ℝ) : phaseDen c=30*(c^2-1/12)^2+92/3 := by
  unfold phaseDen
  ring

theorem phaseDen_lower (c : ℝ) : 92/3≤phaseDen c := by
  rw [phaseDen_square]
  nlinarith [sq_nonneg (c^2-1/12)]

theorem phaseDen_pos (c : ℝ) : 0<phaseDen c := by linarith [phaseDen_lower c]

theorem phaseDen_even (c : ℝ) : phaseDen (-c)=phaseDen c := by unfold phaseDen; ring

theorem phaseRate_odd (c : ℝ) : phaseRate (-c)= -phaseRate c := by
  rw [phaseRate_formula,phaseRate_formula,phaseDen_even]
  ring

theorem phaseRate_zero_iff (c : ℝ) : phaseRate c=0 ↔ c=0 := by
  rw [phaseRate_formula,div_eq_zero_iff]
  simp only [(phaseDen_pos c).ne',or_false]
  constructor <;> intro h <;> linarith

theorem phaseRate_negative_iff (c : ℝ) : phaseRate c<0 ↔ 0<c := by
  rw [phaseRate_formula,div_lt_iff₀ (phaseDen_pos c)]
  constructor <;> intro h <;> linarith

theorem phaseRate_positive_iff (c : ℝ) : 0<phaseRate c ↔ c<0 := by
  rw [phaseRate_formula,lt_div_iff₀ (phaseDen_pos c)]
  constructor <;> intro h <;> linarith

theorem phaseRate_continuous : Continuous phaseRate := by
  have he : phaseRate=(fun c => -48*c/phaseDen c) := funext phaseRate_formula
  rw [he]
  exact (continuous_const.mul continuous_id).div (by unfold phaseDen; fun_prop)
    (fun c => (phaseDen_pos c).ne')

theorem phaseRate_norm_bound (c : ℝ) : ‖phaseRate c‖≤(36/23 : ℝ)*|c| := by
  rw [phaseRate_formula,Real.norm_eq_abs,abs_div,abs_mul,abs_of_pos (phaseDen_pos c)]
  norm_num
  apply (div_le_iff₀ (phaseDen_pos c)).mpr
  have hm := mul_le_mul_of_nonneg_left (phaseDen_lower c) (abs_nonneg c)
  nlinarith

theorem phaseRate_memLp : MemLp phaseRate 2 γ := by
  have hi : MemLp (fun c : ℝ => c) 2 γ := by
    simpa using GaussianCore.polynomial_memLp (X : Polynomial ℝ) 2 (by norm_num)
  have hg : MemLp (fun c : ℝ => (36/23 : ℝ)*|c|) 2 γ := by
    simpa only [Real.norm_eq_abs] using hi.norm.const_mul (36/23 : ℝ)
  exact hg.mono' phaseRate_continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall phaseRate_norm_bound)

theorem phaseRate_integrable : Integrable phaseRate γ := phaseRate_memLp.integrable (by norm_num)
theorem phaseRate_sq_integrable : Integrable (fun c => (phaseRate c)^2) γ := phaseRate_memLp.integrable_sq

theorem gaussian_neg_preserving : MeasurePreserving (fun c : ℝ => -c) γ γ := by
  refine ⟨measurable_neg,?_⟩
  simpa using (gaussianReal_map_neg (μ := 0) (v := 1))

theorem phaseRate_mean_zero : (∫ c, phaseRate c ∂γ)=0 := by
  have he := gaussian_neg_preserving.integral_comp measurableEmbedding_neg phaseRate
  simp_rw [phaseRate_odd] at he
  rw [integral_neg] at he
  linarith

theorem square_support_measure : γ (Function.support (fun c => (phaseRate c)^2))=1 := by
  have hs : Function.support (fun c => (phaseRate c)^2)=({0} : Set ℝ)ᶜ := by
    ext c
    simp only [Function.mem_support,ne_eq,sq_eq_zero_iff,phaseRate_zero_iff,
      mem_compl_iff,mem_singleton_iff]
  rw [hs,measure_compl (measurableSet_singleton 0) (by simp)]
  simp

theorem phaseRate_second_moment_pos : 0<∫ c, (phaseRate c)^2 ∂γ := by
  apply (integral_pos_iff_support_of_nonneg (fun c => sq_nonneg (phaseRate c))
    phaseRate_sq_integrable).mpr
  rw [square_support_measure]
  norm_num

theorem centered_second_moment_pos :
    0<∫ c, (phaseRate c-(∫ z, phaseRate z ∂γ))^2 ∂γ := by
  simpa only [phaseRate_mean_zero,sub_zero] using phaseRate_second_moment_pos

def rateL2 : Lp ℝ 2 γ := phaseRate_memLp.toLp phaseRate
theorem rateL2_coeFn : rateL2 =ᵐ[γ] phaseRate := MemLp.coeFn_toLp _

theorem rateL2_ne_zero : rateL2≠0 := by
  intro hz
  have he := rateL2_coeFn
  rw [hz] at he
  have hzero : phaseRate =ᵐ[γ] (0 : ℝ → ℝ) := he.symm.trans (Lp.coeFn_zero ℝ 2 γ)
  have hs : (fun c => (phaseRate c)^2) =ᵐ[γ] (0 : ℝ → ℝ) := by
    filter_upwards [hzero] with c hc
    simp only [Pi.zero_apply] at hc ⊢
    rw [hc]
    norm_num
  have hi : (∫ c, (phaseRate c)^2 ∂γ)=0 := by rw [integral_congr_ae hs]; simp
  linarith [phaseRate_second_moment_pos]

theorem rateL2_norm_pos : 0<‖rateL2‖ := norm_pos_iff.mpr rateL2_ne_zero

theorem linear_product_integrable : Integrable (fun c => phaseRate c*c) γ := by
  have hi : MemLp (fun c : ℝ => c) 2 γ := by
    simpa using GaussianCore.polynomial_memLp (X : Polynomial ℝ) 2 (by norm_num)
  have hm : MemLp (fun c => phaseRate c*c) 1 γ := mul_memLp phaseRate_memLp hi
  exact hm.integrable (by norm_num)

theorem linear_product_formula (c : ℝ) : phaseRate c*c= -48*c^2/phaseDen c := by
  rw [phaseRate_formula]
  ring

theorem linear_product_nonpos (c : ℝ) : phaseRate c*c≤0 := by
  rw [linear_product_formula]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg c]) (phaseDen_pos c).le

theorem negative_linear_support_measure :
    γ (Function.support (fun c => -(phaseRate c*c)))=1 := by
  have hs : Function.support (fun c => -(phaseRate c*c))=({0} : Set ℝ)ᶜ := by
    ext c
    simp [Function.mem_support,mul_eq_zero,phaseRate_zero_iff]
  rw [hs,measure_compl (measurableSet_singleton 0) (by simp)]
  simp

theorem linear_correlation_negative : (∫ c, phaseRate c*c ∂γ)<0 := by
  have hp : 0<∫ c, -(phaseRate c*c) ∂γ := by
    apply (integral_pos_iff_support_of_nonneg
      (fun c => neg_nonneg.mpr (linear_product_nonpos c)) linear_product_integrable.neg).mpr
    rw [negative_linear_support_measure]
    norm_num
  rw [integral_neg] at hp
  linarith

theorem sample_velocity (c : ℝ) :
    ContDiff ℝ ⊤ (ParameterizedTriadRepresentative.velocity 2 1 c) ∧
    (∀ x, ParameterizedTriadRepresentative.divergence 2 1 c x=0) ∧
    (∃ x, ParameterizedTriadRepresentative.velocity 2 1 c x≠0) :=
  ⟨ParameterizedTriadRepresentative.velocity_smooth _ _ _,
    ParameterizedTriadRepresentative.divergence_zero _ _ _,
    ParameterizedTriadRepresentative.velocity_nonzero _ _ _ (phase_energy_pos c)⟩

end OperatorDerivativeRewrite.Foundation.GaussianTriadPhase
