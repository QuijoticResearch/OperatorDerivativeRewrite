import Foundation.FractionalFourierGraphCore
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Group.Tannery
open MeasureTheory Filter Set AddCircle
open scoped Topology NNReal
/-! Strongly continuous diagonal contractions on actual normalized Haar L2.
Right norm derivatives have EXACTLY the maximal Fourier multiplier graph.
Fractional rates recover -|n|^gamma and the unsmoothed generator graph core.
This is an operator semigroup: positivity/Markov realization, drifted domains,
pointwise Gamma extension and sharp functional inequalities are not asserted. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FractionalFourierSemigroup
open FractionalFourierGraphCore
abbrev Coeff := lp (fun _ : ℤ => ℂ) 2
def multiplier (a : ℤ → ℝ≥0) (t : ℝ≥0) (n : ℤ) : ℂ :=
  (Real.exp (-(a n : ℝ)*(t:ℝ)) : ℂ)
theorem multiplier_bound (a : ℤ → ℝ≥0) (t : ℝ≥0) (n : ℤ) : ‖multiplier a t n‖ ≤ 1 := by
  simp only [multiplier,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (a n).coe_nonneg) t.coe_nonneg)
def term (a : ℤ → ℝ≥0) (t : ℝ≥0) (n : ℤ) : ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (multiplier a t n)
theorem term_bound (a : ℤ → ℝ≥0) (t : ℝ≥0) (n : ℤ) : ‖term a t n‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z * multiplier a t n‖ ≤ 1*‖z‖
  rw [norm_mul]
  nlinarith [multiplier_bound a t n,norm_nonneg z]
def coefficients (a : ℤ → ℝ≥0) (t : ℝ≥0) : Coeff →L[ℂ] Coeff :=
  lp.mapCLM 2 (term a t) zero_le_one (term_bound a t)
theorem coefficients_apply (a : ℤ → ℝ≥0) (t : ℝ≥0) (f : Coeff) (n : ℤ) :
    coefficients a t f n = f n * multiplier a t n := rfl
def evolution (a : ℤ → ℝ≥0) (t : ℝ≥0) : E →L[ℂ] E :=
  basis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((coefficients a t).comp basis.repr.toContinuousLinearEquiv.toContinuousLinearMap)
theorem evolution_coeff (a : ℤ → ℝ≥0) (t : ℝ≥0) (f : E) (n : ℤ) :
    basis.repr (evolution a t f) n = basis.repr f n * multiplier a t n := by
  change basis.repr (basis.repr.symm (coefficients a t (basis.repr f))) n = _
  rw [LinearIsometryEquiv.apply_symm_apply,coefficients_apply]
theorem contraction (a : ℤ → ℝ≥0) (t : ℝ≥0) (f : E) : ‖evolution a t f‖ ≤ ‖f‖ := by
  have h := (coefficients a t).le_of_opNorm_le (lp.norm_mapCLM_le 2 (term a t) zero_le_one (term_bound a t)) (basis.repr f)
  simpa [evolution] using h
theorem evolution_zero (a : ℤ → ℝ≥0) (f : E) : evolution a 0 f = f := by
  apply basis.repr.injective
  ext n
  simp [evolution_coeff,multiplier]
theorem evolution_add (a : ℤ → ℝ≥0) (s t : ℝ≥0) (f : E) :
    evolution a s (evolution a t f) = evolution a (s+t) f := by
  apply basis.repr.injective
  ext n
  simp only [evolution_coeff,multiplier,NNReal.coe_add,mul_add,Real.exp_add,Complex.ofReal_mul]
  ring
theorem coefficient_square_sum (f : E) :
    HasSum (fun n => ‖basis.repr f n‖^2) (‖f‖^2) := by
  simpa [Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) (basis.repr f)
theorem norm_limit_of_coefficients {ι : Type*} {l : Filter ι} (F : ι → E) (g : E)
    (b : ℤ → ℝ) (hb : Summable (fun n => (b n)^2))
    (hc : ∀ n, Tendsto (fun i => basis.repr (F i) n) l (𝓝 (basis.repr g n)))
    (hbound : ∀ᶠ i in l, ∀ n, ‖basis.repr (F i-g) n‖ ≤ b n) :
    Tendsto F l (𝓝 g) := by
  have hn (n : ℤ) : Tendsto (fun i => ‖basis.repr (F i-g) n‖^2) l (𝓝 0) := by
    have h := ((hc n).sub (tendsto_const_nhds (x := basis.repr g n))).norm.pow 2
    simpa using h
  have ht := tendsto_tsum_of_dominated_convergence hb hn
    (hbound.mono fun i hi n => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hi n) 2)
  have ht' : Tendsto (fun i => ‖F i-g‖^2) l (𝓝 0) := by
    simpa only [(coefficient_square_sum _).tsum_eq,tsum_zero] using ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh
theorem strong_continuity (a : ℤ → ℝ≥0) (f : E) : Continuous (fun t => evolution a t f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply norm_limit_of_coefficients _ _ (fun n => 2*‖basis.repr f n‖)
  · have h := (coefficient_square_sum f).summable.mul_left 4
    convert h using 1
    ext n
    ring
  · intro n
    simp only [evolution_coeff,multiplier]
    exact (show Continuous (fun t : ℝ≥0 => basis.repr f n * (Real.exp (-(a n : ℝ)*(t:ℝ)) : ℂ)) by fun_prop).continuousAt.tendsto
  · exact Eventually.of_forall fun t n => by
      simp only [map_sub,lp.coeFn_sub,Pi.sub_apply,evolution_coeff]
      calc
        ‖basis.repr f n * multiplier a t n - basis.repr f n * multiplier a s n‖ ≤
            ‖basis.repr f n * multiplier a t n‖ + ‖basis.repr f n * multiplier a s n‖ := norm_sub_le _ _
        _ ≤ 2*‖basis.repr f n‖ := by
          rw [norm_mul,norm_mul]
          nlinarith [multiplier_bound a t n,multiplier_bound a s n,norm_nonneg (basis.repr f n)]

def slope (a : ℤ → ℝ≥0) (f : E) (t : ℝ) : E :=
  (t⁻¹:ℂ) • (evolution a t.toNNReal f-f)
theorem real_quotient_bound (b t : ℝ) (hb : 0 ≤ b) (ht : 0 < t) :
    |t⁻¹*(Real.exp (-b*t)-1)| ≤ b := by
  have hu : Real.exp (-b*t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) ht.le)
  have hl := Real.add_one_le_exp (-b*t)
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) (sub_nonpos.mpr hu))]
  have he : -(t⁻¹*(Real.exp (-b*t)-1)) = (1-Real.exp (-b*t))/t := by ring
  rw [he,div_le_iff₀ ht]
  nlinarith
theorem real_quotient_limit (b : ℝ) :
    Tendsto (fun t : ℝ => t⁻¹*(Real.exp (-b*t)-1)) (𝓝[>] 0) (𝓝 (-b)) := by
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-b*t)) (-b) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul (-b)).exp
  simpa using hd.tendsto_slope_zero_right
theorem slope_coeff (a : ℤ → ℝ≥0) (f : E) (t : ℝ) (ht : 0 ≤ t) (n : ℤ) :
    basis.repr (slope a f t) n =
      (t⁻¹*(Real.exp (-(a n : ℝ)*t)-1):ℝ) * basis.repr f n := by
  simp only [slope,map_smul,map_sub,lp.coeFn_smul,lp.coeFn_sub,Pi.smul_apply,Pi.sub_apply,
    evolution_coeff,multiplier,Real.coe_toNNReal t ht,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_inv]
  ring
theorem slope_coefficient_limit (a : ℤ → ℝ≥0) (f : E) (n : ℤ) :
    Tendsto (fun t => basis.repr (slope a f t) n) (𝓝[>] 0)
      (𝓝 (-((a n : ℝ):ℂ)*basis.repr f n)) := by
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp (real_quotient_limit (a n))).mul_const (basis.repr f n)
  simp only [Complex.ofReal_neg] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (slope_coeff a f t (le_of_lt ht) n).symm

theorem slope_coefficient_bound (a : ℤ → ℝ≥0) (f g : E)
    (h : (f,g) ∈ graph (fun n => -((a n : ℝ):ℂ))) (t : ℝ) (ht : 0 < t) (n : ℤ) :
    ‖basis.repr (slope a f t) n‖ ≤ ‖basis.repr g n‖ := by
  rw [slope_coeff a f t ht.le n, h n, norm_mul,norm_mul,norm_neg,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (a n).coe_nonneg]
  exact mul_le_mul_of_nonneg_right (real_quotient_bound (a n) t (a n).coe_nonneg ht) (norm_nonneg _)
theorem graph_slope_limit (a : ℤ → ℝ≥0) (f g : E)
    (h : (f,g) ∈ graph (fun n => -((a n : ℝ):ℂ))) :
    Tendsto (slope a f) (𝓝[>] 0) (𝓝 g) := by
  apply norm_limit_of_coefficients _ _ (fun n => 2*‖basis.repr g n‖)
  · have hs := (coefficient_square_sum g).summable.mul_left 4
    convert hs using 1
    ext n
    ring
  · intro n
    rw [h n]
    exact slope_coefficient_limit a f n
  · filter_upwards [self_mem_nhdsWithin] with t ht n
    simp only [map_sub,lp.coeFn_sub,Pi.sub_apply]
    calc
      ‖basis.repr (slope a f t) n-basis.repr g n‖ ≤
          ‖basis.repr (slope a f t) n‖+‖basis.repr g n‖ := norm_sub_le _ _
      _ ≤ 2*‖basis.repr g n‖ := by linarith [slope_coefficient_bound a f g h t ht n]
theorem slope_limit_graph (a : ℤ → ℝ≥0) (f g : E)
    (h : Tendsto (slope a f) (𝓝[>] 0) (𝓝 g)) :
    (f,g) ∈ graph (fun n => -((a n : ℝ):ℂ)) := by
  intro n
  have hc : Continuous (fun f : E => basis.repr f n) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp basis.repr.continuous
  exact tendsto_nhds_unique (hc.continuousAt.tendsto.comp h) (slope_coefficient_limit a f n)
theorem generator_iff (a : ℤ → ℝ≥0) (f g : E) :
    Tendsto (slope a f) (𝓝[>] 0) (𝓝 g) ↔
      (f,g) ∈ graph (fun n => -((a n : ℝ):ℂ)) :=
  ⟨slope_limit_graph a f g,graph_slope_limit a f g⟩
def rates (γ : ℝ) (n : ℤ) : ℝ≥0 := ⟨|(n:ℝ)|^γ,Real.rpow_nonneg (abs_nonneg _) _⟩
theorem fractional_generator_iff (γ : ℝ) (f g : E) :
    Tendsto (slope (rates γ) f) (𝓝[>] 0) (𝓝 g) ↔
      (f,g) ∈ graph (fractionalSymbol γ) := generator_iff _ _ _

theorem actual_fourier_evolution (γ : ℝ) (t : ℝ≥0) (f : E) (n : ℤ) :
    fourierCoeff (evolution (rates γ) t f) n =
      fourierCoeff f n * (Real.exp (-(|(n:ℝ)|^γ)*(t:ℝ)) : ℂ) := by
  have h := evolution_coeff (rates γ) t f n
  have hr : ((rates γ n : ℝ≥0):ℝ) = |(n:ℝ)|^γ := rfl
  rw [multiplier,hr] at h
  simpa only [basis,fourierBasis_repr] using h
theorem fractional_generator_domain (γ : ℝ) (f : E) :
    (∃ g : E, Tendsto (slope (rates γ) f) (𝓝[>] 0) (𝓝 g)) ↔
      Memℓp (fun n : ℤ => -((|(n:ℝ)|^γ:ℝ):ℂ)*fourierCoeff f n) 2 := by
  simp only [fractional_generator_iff]
  simpa only [fractionalSymbol,basis,fourierBasis_repr] using graph_domain_iff (fractionalSymbol γ) f
theorem fractional_time_core (γ : ℝ) :
    closure {p : E × E | Tendsto (slope (rates γ) p.1) (𝓝[>] 0) (𝓝 p.2) ∧ p.1 ∈ finiteCore} =
      {p : E × E | Tendsto (slope (rates γ) p.1) (𝓝[>] 0) (𝓝 p.2)} := by
  simpa only [fractional_generator_iff,finiteGraph,graph,mem_ofPred_eq] using fractional_graph_core γ

end OperatorDerivativeRewrite.Foundation.FractionalFourierSemigroup
