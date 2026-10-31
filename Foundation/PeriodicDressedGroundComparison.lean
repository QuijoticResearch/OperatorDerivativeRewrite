import Foundation.PeriodicPhysicalKineticReduction
import Foundation.PeriodicQuarticCurvature
/-! A global comparison obstruction for the actual periodic Wilson ground.
The constructed dressed ground cannot have coupling-uniform global oscillation.
This is a fixed-cell weight-comparison obstruction, not a spectral obstruction.
Local kinetic-neighborhood comparisons and physical mass gaps remain open. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicDressedGroundComparison
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicPhysicalKineticReduction CubeHaarUpper

theorem dressed_comparison_obstruction {β : ℝ} (hb : 0 ≤ β) (g : GroundData β)
    (U : State) (C : ℝ)
    (hC : ∀ V,multiplier β V*g.function V ≤ C*(multiplier β U*g.function U)) :
    g.value ≤ laplace β^192*C*Real.exp (-β*spatialAction U) := by
  have hd : Integrable (kineticDensity β U) boundaryHaar := by
    apply Integrable.of_integral_ne_zero
    rw [kinetic_mass β hb]
    exact one_ne_zero
  have hm (V : State) : 0 ≤ kineticDensity β U V :=
    (div_pos (Real.exp_pos _) (pow_pos (laplace_pos β hb) _)).le
  have hTw : kinetic β (fun V => multiplier β V*g.function V) U ≤
      C*(multiplier β U*g.function U) := by
    unfold kinetic
    have h := integral_mono_of_nonneg
      (ae_of_all _ (fun V => mul_nonneg (hm V) (mul_pos (Real.exp_pos _) (g.function_pos V)).le))
      (hd.mul_const (C*(multiplier β U*g.function U)))
      (ae_of_all _ (fun V => mul_le_mul_of_nonneg_left (hC V) (hm V)))
    simpa only [integral_mul_const,kinetic_mass β hb,one_mul,multiplier] using h
  have hp : 0 < laplace β^192*multiplier β U :=
    mul_pos (pow_pos (laplace_pos β hb) _) (Real.exp_pos _)
  have he := mul_le_mul_of_nonneg_left hTw hp.le
  rw [dressed_ground_equation hb g U] at he
  have hs : multiplier β U*multiplier β U=Real.exp (-β*spatialAction U) := by
    unfold multiplier
    rw [← Real.exp_add]
    congr 1
    ring
  have hr : laplace β^192*multiplier β U*(C*(multiplier β U*g.function U))=
      (laplace β^192*C*Real.exp (-β*spatialAction U))*g.function U := by
    rw [← hs]
    ring
  rw [hr] at he
  exact (mul_le_mul_iff_left₀ (g.function_pos U)).mp (by simpa only [mul_comm] using he)

open PeriodicGroundHaarScale
private theorem laplace_power_upper (β : ℝ) (hb : 1 ≤ β) :
    laplace β^192 ≤ upperConstant/β^288 := by
  have hp : 0 < β := by linarith
  let t : ℝ := 1/Real.sqrt β
  have ht : 0 < t := div_pos zero_lt_one (Real.sqrt_pos.mpr hp)
  have h1 : t ≤ 1 := (div_le_one (Real.sqrt_pos.mpr hp)).mpr (by simpa using Real.sqrt_le_sqrt hb)
  have ht2 : t^2=1/β := by dsimp [t]; rw [div_pow,one_pow,Real.sq_sqrt hp.le]
  have he : 1/t^2=β := by rw [ht2]; field_simp
  have hu := SU2HaarLaplaceUpper.laplace_scaled_upper 1 t (by norm_num) ht h1
  rw [he] at hu
  have hpow := pow_le_pow_left₀ (laplace_pos β hp.le).le hu 192
  rw [mul_pow] at hpow
  have ht576 : (t^3)^192=1/β^288 := by
    calc
      _ = (t^2)^288 := by ring
      _ = _ := by rw [ht2,div_pow,one_pow]
  rw [ht576] at hpow
  simpa only [upperConstant,mul_one_div] using hpow

theorem actual_comparison_lower {β : ℝ} (hb : 16777216 ≤ β) (g : GroundData β)
    (U : State) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ V,multiplier β V*g.function V ≤ C*(multiplier β U*g.function U)) :
    PeriodicGaugeSaturatedGround.eigenLowerConstant ≤
      upperConstant*C*Real.exp (-β*spatialAction U) := by
  have hp : 0 < β := by linarith
  have h1 := dressed_comparison_obstruction hp.le g U C hC
  have h2 := mul_le_mul_of_nonneg_right (laplace_power_upper β (by linarith))
    (mul_nonneg hC0 (Real.exp_pos (-β*spatialAction U)).le)
  have h3 := PeriodicGaugeSaturatedGround.eigenvalue_matching_lower β hb g
  have h4 : PeriodicGaugeSaturatedGround.eigenLowerConstant/β^288 ≤
      (upperConstant*C*Real.exp (-β*spatialAction U))/β^288 := by
    calc
      _ ≤ g.value := h3
      _ ≤ laplace β^192*C*Real.exp (-β*spatialAction U) := h1
      _ ≤ (upperConstant/β^288)*(C*Real.exp (-β*spatialAction U)) := by nlinarith [h2]
      _ = _ := by ring
  exact (div_le_div_iff_of_pos_right (pow_pos hp 288)).mp h4

/-- Every actual ground violates any fixed global comparison, eventually in
coupling, at every fixed positive-action reference field. -/
theorem eventual_comparison_failure (U : State) (hS : 0 < spatialAction U)
    (C : ℝ) (hC0 : 0 ≤ C) :
    ∀ᶠ β : ℝ in atTop,∀ g : GroundData β,∃ V,
      C*(multiplier β U*g.function U) < multiplier β V*g.function V := by
  have ht : Tendsto (fun β : ℝ => upperConstant*C*Real.exp (-β*spatialAction U)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hS)).const_mul
      (upperConstant*C)
    simpa only [Function.comp_apply,id_eq,mul_zero,neg_mul] using h
  have hs := (tendsto_order.1 ht).2 _ PeriodicGaugeSaturatedGround.eigenLowerConstant_pos
  filter_upwards [hs,eventually_ge_atTop (16777216 : ℝ)] with β hsmall hlarge
  intro g
  by_contra! hC
  exact (not_lt_of_ge (actual_comparison_lower hlarge g U C hC0 hC)) hsmall

/-- No choice of the already constructed grounds can restore an eventual
coupling-uniform global weight ratio. Scaling the eigenfunctions cannot help. -/
theorem no_eventual_uniform_comparison (G : (β : ℝ) → GroundData β)
    (U : State) (hS : 0 < spatialAction U) (C : ℝ) (hC0 : 0 ≤ C) :
    ¬ (∀ᶠ β : ℝ in atTop,∀ V,
      multiplier β V*(G β).function V ≤ C*(multiplier β U*(G β).function U)) := by
  intro hh
  obtain ⟨β,hbad,hgood⟩ := ((eventual_comparison_failure U hS C hC0).and hh).exists
  obtain ⟨V,hV⟩ := hbad (G β)
  exact (not_lt_of_ge (hgood V)) hV

/-- A concrete genuine lattice reference has exact spatial action128. -/
theorem quartic_no_uniform_comparison (G : (β : ℝ) → GroundData β) :
    ¬ ∃ C : ℝ,0 ≤ C ∧ ∀ᶠ β : ℝ in atTop,∀ V,
      multiplier β V*(G β).function V ≤
        C*(multiplier β (PeriodicQuarticCurvature.field (Real.pi/2))*
          (G β).function (PeriodicQuarticCurvature.field (Real.pi/2))) := by
  rintro ⟨C,hC,hh⟩
  apply no_eventual_uniform_comparison G (PeriodicQuarticCurvature.field (Real.pi/2)) _ C hC hh
  rw [PeriodicQuarticCurvature.spatial_action,Real.sin_pi_div_two]
  norm_num
end OperatorDerivativeRewrite.Foundation.PeriodicDressedGroundComparison
