import Foundation.RiemannRealOrderFractionalCoefficient

/-! A precise obstruction to relative asymptotics uniform over orders near one.
No claim about uniform absolute errors or the reality of quadratic zeros is made. -/
noncomputable section
open Set Filter Complex
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannRealOrderRelativeObstruction
open RiemannRealOrderFractionalCoefficient

def scaledValue (a t x : ℝ) : ℂ :=
  ((x^(2*a+1) : ℝ) : ℂ)*RiemannRealOrderFlow.flow a t (x : ℂ)

theorem scaledValue_continuousAt_one (t x : ℝ) (hx : 0 < x) :
    ContinuousAt (fun a : ℝ => scaledValue a t x) 1 := by
  have hp : ContinuousAt (fun a : ℝ => x^(2*a+1)) 1 :=
    (Real.continuousAt_const_rpow hx.ne').comp (by fun_prop)
  have hf : ContinuousAt (fun a : ℝ => RiemannRealOrderFlow.flow a t (x : ℂ)) 1 := by
    have h := (RiemannRealOrderZeroLimits.flow_joint_continuousAt 1 (by norm_num) t (x : ℂ)).comp
      (f := fun a : ℝ => (a,(x : ℂ)))
      (show ContinuousAt (fun a : ℝ => (a,(x : ℂ))) 1 by fun_prop)
    simpa only [Function.comp_def] using h
  exact (Complex.continuous_ofReal.continuousAt.comp hp).mul hf

theorem scaledValue_one_ne_zero (t x : ℝ) (hx : 0 < x)
    (hf : RiemannRealOrderFlow.flow 1 t (x : ℂ) ≠ 0) : scaledValue 1 t x ≠ 0 := by
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hx _).ne') hf

theorem relative_bound_fails_near_one (t x M : ℝ) (hx : 0 < x)
    (hf : RiemannRealOrderFlow.flow 1 t (x : ℂ) ≠ 0) :
    ∀ᶠ a : ℝ in 𝓝[>] 1,
      M*|leading a t| < ‖scaledValue a t x-(leading a t : ℂ)‖ := by
  have hL := (leading_hasDerivAt_one t).continuousAt
  have hv := (scaledValue_continuousAt_one t x hx).sub (Complex.continuous_ofReal.continuousAt.comp hL)
  have hg : ContinuousAt (fun a : ℝ =>
      ‖scaledValue a t x-(leading a t : ℂ)‖-M*|leading a t|) 1 :=
    hv.norm.sub (continuousAt_const.mul hL.abs)
  have hlim : Tendsto (fun a : ℝ => ‖scaledValue a t x-(leading a t : ℂ)‖-M*|leading a t|)
      (𝓝[>] 1) (𝓝 ‖scaledValue 1 t x‖) := by
    simpa only [leading_one,Complex.ofReal_zero,sub_zero,abs_zero,mul_zero] using
      hg.tendsto.mono_left nhdsWithin_le_nhds
  have he := hlim.eventually (Ioi_mem_nhds (norm_pos_iff.mpr (scaledValue_one_ne_zero t x hx hf)))
  filter_upwards [he] with a ha
  change 0 < ‖scaledValue a t x-(leading a t : ℂ)‖-M*|leading a t| at ha
  linarith

theorem exists_far_quadratic_nonzero (t R : ℝ) :
    ∃ x : ℝ, R ≤ x ∧ 0 < x ∧ RiemannRealOrderFlow.flow 1 t (x : ℂ) ≠ 0 := by
  let B := max R 1
  let K : Set ℂ := Complex.ofReal '' Icc B (B+1)
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hZ := RiemannRealOrderFractionalZeros.compact_zero_set_finite 1 t (by norm_num) K hK
  have hpre : (Complex.ofReal ⁻¹' (K ∩ (RiemannRealOrderFlow.flow 1 t) ⁻¹' {0})).Finite :=
    Set.Finite.preimage (fun x _ y _ h => Complex.ofReal_injective h) hZ
  have hI : (Icc B (B+1)).Infinite := Icc_infinite (by linarith)
  obtain ⟨x,hx,hnot⟩ := (hI.sdiff hpre).nonempty
  refine ⟨x,(le_max_left R 1).trans hx.1,
    lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one (le_max_right R 1)) hx.1,?_⟩
  intro hz
  apply hnot
  exact ⟨⟨x,hx,rfl⟩,hz⟩

theorem uniform_relative_bound_counterexample (t δ R M : ℝ) (hδ : 0 < δ) :
    ∃ a x : ℝ, 1 < a ∧ a < 1+δ ∧ a < 3/2 ∧ 0 < x ∧ R ≤ x ∧
      M*|leading a t| < ‖scaledValue a t x-(leading a t : ℂ)‖ := by
  obtain ⟨x,hxR,hx,hf⟩ := exists_far_quadratic_nonzero t R
  have hb := relative_bound_fails_near_one t x M hx hf
  have hu : ∀ᶠ a : ℝ in 𝓝 (1 : ℝ), a < min (1+δ) (3/2) :=
    Iio_mem_nhds (lt_min (by linarith) (by norm_num))
  have hupper : ∀ᶠ a : ℝ in 𝓝[>] 1, a < min (1+δ) (3/2) :=
    hu.filter_mono nhdsWithin_le_nhds
  obtain ⟨a,ha⟩ := ((hb.and hupper).and self_mem_nhdsWithin).exists
  exact ⟨a,x,ha.2,ha.1.2.trans_le (min_le_left _ _),
    ha.1.2.trans_le (min_le_right _ _),hx,hxR,ha.1.1⟩

theorem no_uniform_relative_bound (t : ℝ) :
    ¬ ∃ δ : ℝ, 0 < δ ∧ ∃ R M : ℝ, ∀ a : ℝ, 1 < a → a < 1+δ → a < 3/2 →
      ∀ x : ℝ, 0 < x → R ≤ x →
        ‖scaledValue a t x-(leading a t : ℂ)‖ ≤ M*|leading a t| := by
  rintro ⟨δ,hδ,R,M,hB⟩
  obtain ⟨a,x,ha,haδ,ha3,hx,hxR,hbad⟩ := uniform_relative_bound_counterexample t δ R M hδ
  exact (not_lt_of_ge (hB a ha haδ ha3 x hx hxR)) hbad

theorem uniform_relative_error_unbounded (t δ R M : ℝ) (ht : t ≠ 0) (hδ : 0 < δ) :
    ∃ a x : ℝ, 1 < a ∧ a < 1+δ ∧ a < 3/2 ∧ 0 < x ∧ R ≤ x ∧
      M < ‖scaledValue a t x/(leading a t : ℂ)-1‖ := by
  obtain ⟨a,x,ha,haδ,ha3,hx,hxR,hbad⟩ := uniform_relative_bound_counterexample t δ R M hδ
  refine ⟨a,x,ha,haδ,ha3,hx,hxR,?_⟩
  have hL := leading_ne_zero a t ha (by linarith) ht
  have he : scaledValue a t x/(leading a t : ℂ)-1=
      (scaledValue a t x-(leading a t : ℂ))/(leading a t : ℂ) := by
    field_simp [Complex.ofReal_ne_zero.mpr hL]
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs]
  exact (lt_div_iff₀ (abs_pos.mpr hL)).mpr hbad

end OperatorDerivativeRewrite.Foundation.RiemannRealOrderRelativeObstruction
