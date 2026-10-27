import Foundation.AnisotropicStableGamma
import Foundation.FractionalFourierSemigroup
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Group.Tannery
open Filter Set
open scoped Topology NNReal
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.WaveDiagonalSemigroup
open FiniteFourierDifferentialTrace AnisotropicStableGamma

abbrev E := lp (fun _ : Wave => ℂ) 2
def rate (a γ : Fin 3 → ℝ) (ha : ∀ j, 0 ≤ a j) (k : Wave) : ℝ≥0 :=
  ⟨anisotropicSymbol a γ k, by
    unfold anisotropicSymbol
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (ha j) (Real.rpow_nonneg (abs_nonneg _) _)⟩

def multiplier (r : Wave → ℝ≥0) (t : ℝ≥0) (k : Wave) : ℂ :=
  (Real.exp (-(r k : ℝ)*(t:ℝ)) : ℂ)
theorem multiplier_bound (r : Wave → ℝ≥0) (t : ℝ≥0) (k : Wave) :
    ‖multiplier r t k‖ ≤ 1 := by
  simp only [multiplier,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (r k).coe_nonneg) t.coe_nonneg)
def term (r : Wave → ℝ≥0) (t : ℝ≥0) (k : Wave) : ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.id ℂ ℂ).smulRight (multiplier r t k)
theorem term_bound (r : Wave → ℝ≥0) (t : ℝ≥0) (k : Wave) : ‖term r t k‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖z * multiplier r t k‖ ≤ 1*‖z‖
  rw [norm_mul]
  nlinarith [multiplier_bound r t k,norm_nonneg z]
def evolution (r : Wave → ℝ≥0) (t : ℝ≥0) : E →L[ℂ] E :=
  lp.mapCLM 2 (term r t) zero_le_one (term_bound r t)
theorem evolution_apply (r : Wave → ℝ≥0) (t : ℝ≥0) (f : E) (k : Wave) :
    evolution r t f k = f k * multiplier r t k := rfl
theorem contraction (r : Wave → ℝ≥0) (t : ℝ≥0) (f : E) :
    ‖evolution r t f‖ ≤ ‖f‖ := by
  simpa using (evolution r t).le_of_opNorm_le
    (lp.norm_mapCLM_le 2 (term r t) zero_le_one (term_bound r t)) f
theorem evolution_zero (r : Wave → ℝ≥0) (f : E) : evolution r 0 f = f := by
  ext k
  simp [evolution_apply,multiplier]
theorem evolution_add (r : Wave → ℝ≥0) (s t : ℝ≥0) (f : E) :
    evolution r s (evolution r t f) = evolution r (s+t) f := by
  ext k
  simp only [evolution_apply,multiplier,NNReal.coe_add,mul_add,Real.exp_add,Complex.ofReal_mul]
  ring

def graph (r : Wave → ℝ≥0) : Set (E × E) :=
  {p | ∀ k, p.2 k = -((r k : ℝ):ℂ) * p.1 k}
theorem graph_closed (r : Wave → ℝ≥0) : IsClosed (graph r) := by
  have hc (k : Wave) : Continuous (fun f : E => f k) :=
    (lp.evalCLM ℂ (fun _ : Wave => ℂ) 2 k).continuous
  have he : graph r = ⋂ k : Wave, {p : E × E | p.2 k = -((r k : ℝ):ℂ) * p.1 k} := by
    ext p
    simp [graph]
  rw [he]
  exact isClosed_iInter fun k => isClosed_eq ((hc k).comp continuous_snd)
    (continuous_const.mul ((hc k).comp continuous_fst))
theorem graph_domain_iff (r : Wave → ℝ≥0) (f : E) :
    (∃ g : E, (f,g) ∈ graph r) ↔
      Memℓp (fun k => -((r k : ℝ):ℂ) * f k) 2 := by
  constructor
  · rintro ⟨g,hg⟩
    have he : (fun k => -((r k : ℝ):ℂ) * f k) = (g : Wave → ℂ) :=
      funext fun k => (hg k).symm
    rw [he]
    exact g.property
  · intro h
    let g : E := ⟨_,h⟩
    exact ⟨g,fun k => rfl⟩

theorem coefficient_square_sum (f : E) :
    HasSum (fun k => ‖f k‖^2) (‖f‖^2) := by
  simpa [Real.rpow_two] using lp.hasSum_norm (p := 2) (by norm_num) f
theorem norm_limit_of_coefficients {ι : Type*} {l : Filter ι} (F : ι → E) (g : E)
    (b : Wave → ℝ) (hb : Summable (fun k => (b k)^2))
    (hc : ∀ k, Tendsto (fun i => F i k) l (𝓝 (g k)))
    (hbound : ∀ᶠ i in l, ∀ k, ‖(F i-g) k‖ ≤ b k) :
    Tendsto F l (𝓝 g) := by
  have hn (k : Wave) : Tendsto (fun i => ‖(F i-g) k‖^2) l (𝓝 0) := by
    have h := ((hc k).sub (tendsto_const_nhds (x := g k))).norm.pow 2
    simpa using h
  have ht := tendsto_tsum_of_dominated_convergence hb hn
    (hbound.mono fun i hi k => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hi k) 2)
  have ht' : Tendsto (fun i => ‖F i-g‖^2) l (𝓝 0) := by
    simpa only [(coefficient_square_sum _).tsum_eq,tsum_zero] using ht
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hh
theorem strong_continuity (r : Wave → ℝ≥0) (f : E) :
    Continuous (fun t => evolution r t f) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply norm_limit_of_coefficients _ _ (fun k => 2*‖f k‖)
  · have h := (coefficient_square_sum f).summable.mul_left 4
    convert h using 1
    ext k
    ring
  · intro k
    simp only [evolution_apply,multiplier]
    exact (show Continuous (fun t : ℝ≥0 => f k * (Real.exp (-(r k : ℝ)*(t:ℝ)) : ℂ)) by
      fun_prop).continuousAt.tendsto
  · exact Eventually.of_forall fun t k => by
      simp only [lp.coeFn_sub,Pi.sub_apply,evolution_apply]
      calc
        ‖f k * multiplier r t k - f k * multiplier r s k‖ ≤
            ‖f k * multiplier r t k‖ + ‖f k * multiplier r s k‖ := norm_sub_le _ _
        _ ≤ 2*‖f k‖ := by
          rw [norm_mul,norm_mul]
          nlinarith [multiplier_bound r t k,multiplier_bound r s k,norm_nonneg (f k)]

def slope (r : Wave → ℝ≥0) (f : E) (t : ℝ) : E :=
  (t⁻¹:ℂ) • (evolution r t.toNNReal f-f)
theorem slope_apply (r : Wave → ℝ≥0) (f : E) (t : ℝ) (ht : 0 ≤ t) (k : Wave) :
    slope r f t k =
      (t⁻¹*(Real.exp (-(r k : ℝ)*t)-1):ℝ) * f k := by
  simp only [slope,lp.coeFn_smul,lp.coeFn_sub,Pi.smul_apply,Pi.sub_apply,
    evolution_apply,multiplier,Real.coe_toNNReal t ht,smul_eq_mul,
    Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_inv]
  ring
theorem slope_coefficient_limit (r : Wave → ℝ≥0) (f : E) (k : Wave) :
    Tendsto (fun t => slope r f t k) (𝓝[>] 0)
      (𝓝 (-((r k : ℝ):ℂ)*f k)) := by
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
    (FractionalFourierSemigroup.real_quotient_limit (r k))).mul_const (f k)
  simp only [Complex.ofReal_neg] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (slope_apply r f t (le_of_lt ht) k).symm
theorem slope_coefficient_bound (r : Wave → ℝ≥0) (f g : E)
    (h : (f,g) ∈ graph r) (t : ℝ) (ht : 0 < t) (k : Wave) :
    ‖slope r f t k‖ ≤ ‖g k‖ := by
  rw [slope_apply r f t ht.le k, h k, norm_mul,norm_mul,norm_neg,
    Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg (r k).coe_nonneg]
  exact mul_le_mul_of_nonneg_right
    (FractionalFourierSemigroup.real_quotient_bound (r k) t (r k).coe_nonneg ht)
    (norm_nonneg _)
theorem graph_slope_limit (r : Wave → ℝ≥0) (f g : E)
    (h : (f,g) ∈ graph r) : Tendsto (slope r f) (𝓝[>] 0) (𝓝 g) := by
  apply norm_limit_of_coefficients _ _ (fun k => 2*‖g k‖)
  · have hs := (coefficient_square_sum g).summable.mul_left 4
    convert hs using 1
    ext k
    ring
  · intro k
    rw [h k]
    exact slope_coefficient_limit r f k
  · filter_upwards [self_mem_nhdsWithin] with t ht k
    simp only [lp.coeFn_sub,Pi.sub_apply]
    calc
      ‖slope r f t k-g k‖ ≤ ‖slope r f t k‖+‖g k‖ := norm_sub_le _ _
      _ ≤ 2*‖g k‖ := by linarith [slope_coefficient_bound r f g h t ht k]
theorem slope_limit_graph (r : Wave → ℝ≥0) (f g : E)
    (h : Tendsto (slope r f) (𝓝[>] 0) (𝓝 g)) : (f,g) ∈ graph r := by
  intro k
  have hc : Continuous (fun f : E => f k) :=
    (lp.evalCLM ℂ (fun _ : Wave => ℂ) 2 k).continuous
  exact tendsto_nhds_unique (hc.continuousAt.tendsto.comp h)
    (slope_coefficient_limit r f k)
theorem generator_iff (r : Wave → ℝ≥0) (f g : E) :
    Tendsto (slope r f) (𝓝[>] 0) (𝓝 g) ↔ (f,g) ∈ graph r :=
  ⟨slope_limit_graph r f g,graph_slope_limit r f g⟩

theorem anisotropic_generator_iff (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (f g : E) :
    Tendsto (slope (rate a γ ha) f) (𝓝[>] 0) (𝓝 g) ↔
      ∀ k, g k = -((anisotropicSymbol a γ k : ℝ):ℂ) * f k := by
  rw [generator_iff]
  constructor
  · intro h k
    exact h k
  · intro h k
    exact h k

theorem anisotropic_generator_domain (a γ : Fin 3 → ℝ)
    (ha : ∀ j, 0 ≤ a j) (f : E) :
    (∃ g : E, Tendsto (slope (rate a γ ha) f) (𝓝[>] 0) (𝓝 g)) ↔
      Memℓp (fun k => -((anisotropicSymbol a γ k : ℝ):ℂ) * f k) 2 := by
  rw [show (∃ g : E, Tendsto (slope (rate a γ ha) f) (𝓝[>] 0) (𝓝 g)) ↔
      (∃ g : E, (f,g) ∈ graph (rate a γ ha)) from
        exists_congr fun g => generator_iff (rate a γ ha) f g]
  rw [graph_domain_iff]
  rfl

def mode (k : Wave) : E := lp.single 2 k (1 : ℂ)
theorem mode_nonzero (k : Wave) : mode k ≠ 0 := by
  intro h
  have h' := congrArg (fun f : E => f k) h
  simp [mode,lp.single_apply] at h'
theorem stationary_mode (r : Wave → ℝ≥0) (k : Wave) (hk : r k = 0)
    (t : ℝ≥0) : evolution r t (mode k) = mode k := by
  ext l
  by_cases h : l = k
  · subst l
    simp [evolution_apply,multiplier,hk,mode,lp.single_apply]
  · simp [evolution_apply,mode,lp.single_apply,h]

end OperatorDerivativeRewrite.Foundation.WaveDiagonalSemigroup
