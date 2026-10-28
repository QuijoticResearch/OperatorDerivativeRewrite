import Foundation.SU2GaugeCovariantTransfer
import Foundation.SU2OneWordLargeCoupling
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Quaternion Topology
namespace OperatorDerivativeRewrite.Foundation.SU2WilsonConvolution
open QuaternionSU2Representation BoundedExponentialTiltResponse

theorem halfTrace_inv (C : SU2) : halfTrace C⁻¹ = halfTrace C := by
  obtain ⟨u,rfl⟩ := hom_surjective C
  rw [← map_inv, halfTrace_map, halfTrace_map, ← Unitary.star_eq_inv]
  simp [QuaternionAngularHaar.realCoordinate]

theorem trace_pair (C D : SU2) :
    halfTrace (C*D) + halfTrace (C*D⁻¹) = 2*halfTrace C*halfTrace D := by
  obtain ⟨u,rfl⟩ := hom_surjective C
  obtain ⟨v,rfl⟩ := hom_surjective D
  rw [← map_inv, ← map_mul, ← map_mul, halfTrace_map, halfTrace_map, halfTrace_map, halfTrace_map]
  change ((u : ℍ)*(v : ℍ)).re + ((u : ℍ)*((v⁻¹ : QuaternionAngularHaar.Group) : ℍ)).re = _
  rw [← Unitary.star_eq_inv]
  simp only [Unitary.coe_star, Quaternion.re_mul, Quaternion.re_star,
    Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star]
  dsimp [QuaternionAngularHaar.realCoordinate]
  ring

def increment (β : ℝ) : Measure SU2 := tiltedMeasure law halfTrace β

theorem increment_probability (β : ℝ) : IsProbabilityMeasure (increment β) :=
  tiltedMeasure_probability law halfTrace halfTrace_measurable halfTrace_bound β

private theorem haar_inv : law.map Inv.inv = law := by
  letI : law.IsMulRightInvariant := ⟨fun g => by
    letI : IsProbabilityMeasure (law.map (fun C => C*g)) := by infer_instance
    exact (law_eq_probability_haar (law.map (fun C => C*g))).symm⟩
  letI : law.inv.IsHaarMeasure := {}
  letI : IsProbabilityMeasure law.inv := by
    change IsProbabilityMeasure (law.map Inv.inv)
    infer_instance
  exact (law_eq_probability_haar law.inv).symm

theorem increment_inv (β : ℝ) : (increment β).map Inv.inv = increment β := by
  have hd : Measurable (fun C : SU2 => ENNReal.ofReal (density law halfTrace β C)) :=
    ((measurable_const.mul halfTrace_measurable).exp.div_const _).ennreal_ofReal
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply measurable_inv hs, increment, tiltedMeasure,
    withDensity_apply _ (measurable_inv hs), withDensity_apply _ hs]
  have he := setLIntegral_map (μ := law) hs hd measurable_inv
  rw [haar_inv] at he
  have hh : (fun C : SU2 => ENNReal.ofReal (density law halfTrace β C)) =
      (fun C => ENNReal.ofReal (density law halfTrace β C⁻¹)) := by
    funext C
    simp [density,halfTrace_inv]
  conv_lhs => rw [hh]
  exact he.symm

def coefficient (β : ℝ) : ℝ := ∫ V, halfTrace V ∂increment β

def step (β : ℝ) (f : SU2 → ℝ) (C : SU2) : ℝ := ∫ V, f (C*V) ∂increment β

private theorem trace_integrable (β : ℝ) (C : SU2) :
    Integrable (fun V => halfTrace (C*V)) (increment β) := by
  letI := increment_probability β
  apply Integrable.mono' (integrable_const (1:ℝ))
    (halfTrace_measurable.comp (measurable_const_mul C)).aestronglyMeasurable
  filter_upwards with V
  change ‖halfTrace (C*V)‖ ≤ 1
  simpa only [Real.norm_eq_abs] using halfTrace_bound (C*V)

theorem halfTrace_eigen (β : ℝ) (C : SU2) :
    step β halfTrace C = coefficient β * halfTrace C := by
  have he := integral_map (μ := increment β) measurable_inv.aemeasurable
    (halfTrace_measurable.comp (measurable_const_mul C)).aestronglyMeasurable
  rw [increment_inv] at he
  have hi : Integrable (fun V => halfTrace (C*V⁻¹)) (increment β) := by
    have him : Integrable (fun V => halfTrace (C*V)) ((increment β).map Inv.inv) := by
      rw [increment_inv]
      exact trace_integrable β C
    exact him.comp_measurable measurable_inv
  have hadd := integral_add (trace_integrable β C) hi
  change (∫ V, halfTrace (C*V)+halfTrace (C*V⁻¹) ∂increment β) = _ at hadd
  have hp : (fun V : SU2 => halfTrace (C*V)+halfTrace (C*V⁻¹)) =
      (fun V => (2*halfTrace C)*halfTrace V) := by
    funext V
    exact trace_pair C V
  rw [hp,integral_const_mul] at hadd
  change (∫ V, halfTrace (C*V) ∂increment β) =
    (∫ V, halfTrace (C*V⁻¹) ∂increment β) at he
  dsimp [step,coefficient]
  linarith


theorem step_actual_kernel (β : ℝ) (f : SU2 → ℝ) (hf : Measurable f) (C : SU2) :
    step β f C = ∫ D, f D ∂SU2OneWordTransfer.transition law β C⁻¹ := by
  rw [SU2GaugeCovariantTransfer.transition_eq_map_tilt, inv_inv]
  rw [integral_map (measurable_const_mul C).aemeasurable hf.aestronglyMeasurable]
  rfl

theorem halfTrace_mul_comm (C D : SU2) : halfTrace (C*D) = halfTrace (D*C) := by
  change (Matrix.trace ((C : SU2TraceHessianModel.M2)*(D : SU2TraceHessianModel.M2))).re/2 = _
  rw [Matrix.trace_mul_comm]
  rfl

theorem trace_sandwich (β : ℝ) (L R : SU2) :
    (∫ V, halfTrace (L*V*R) ∂increment β) = coefficient β * halfTrace (L*R) := by
  have he : (fun V : SU2 => halfTrace (L*V*R)) = fun V => halfTrace ((R*L)*V) := by
    funext V
    rw [halfTrace_mul_comm (L*V) R, ← mul_assoc]
  rw [he]
  change step β halfTrace (R*L) = _
  rw [halfTrace_eigen,halfTrace_mul_comm R L]

/-- Nested expectation over an independent Wilson increment at each oriented edge
occurrence. Repeated occurrences of one physical edge are not identified here. -/
def wordAverage (β : ℝ) : List SU2 → SU2 → ℝ
  | [], C => halfTrace C
  | A::as, C => ∫ V, wordAverage β as (C*A*V) ∂increment β

theorem wordAverage_exact (β : ℝ) (as : List SU2) (C : SU2) :
    wordAverage β as C = coefficient β ^ as.length * halfTrace (C*as.prod) := by
  induction as generalizing C with
  | nil => simp [wordAverage]
  | cons A as ih =>
    simp only [wordAverage, ih, integral_const_mul, List.length_cons, List.prod_cons]
    rw [trace_sandwich, pow_succ]
    simp only [mul_assoc]

def loop4 (A B C D : SU2) : ℝ := halfTrace (A*B*C*D)

theorem loop4_gauge (g₀ g₁ g₂ g₃ A B C D : SU2) :
    loop4 (g₀*A*g₁⁻¹) (g₁*B*g₂⁻¹) (g₂*C*g₃⁻¹) (g₃*D*g₀⁻¹) = loop4 A B C D := by
  unfold loop4
  have he : (g₀*A*g₁⁻¹)*(g₁*B*g₂⁻¹)*(g₂*C*g₃⁻¹)*(g₃*D*g₀⁻¹) =
      g₀*(A*B*C*D)*g₀⁻¹ := by group
  rw [he,halfTrace_conjugate]

theorem loop4_average (β : ℝ) (A B C D : SU2) :
    wordAverage β [A,B,C,D] 1 = coefficient β ^ 4 * loop4 A B C D := by
  rw [wordAverage_exact]
  simp [loop4, mul_assoc]

theorem coefficient_zero : coefficient 0 = 0 := by
  unfold coefficient increment
  rw [SU2StapleExtremes.zero_tilt]
  exact (SU2TiltEnergyResponse.moment_values law).1

theorem coefficient_tendsto_one : Tendsto coefficient atTop (𝓝 1) :=
  SU2OneWordLargeCoupling.positive_mean_tendsto_one

theorem fixed_word_factor_tendsto_one (n : ℕ) :
    Tendsto (fun β => coefficient β ^ n) atTop (𝓝 1) := by
  simpa using coefficient_tendsto_one.pow n

theorem no_uniform_fixed_word_factor (n : ℕ) (q : ℝ) (hq : q < 1) :
    ∃ β : ℝ, 0 ≤ β ∧ q < coefficient β ^ n := by
  have h := (tendsto_order.mp (fixed_word_factor_tendsto_one n)).1 q hq
  exact ((eventually_ge_atTop (0:ℝ)).and h).exists


theorem wordAverage_layer_integrable (β : ℝ) (as : List SU2) (C A : SU2) :
    Integrable (fun V => wordAverage β as (C*A*V)) (increment β) := by
  have he : (fun V => wordAverage β as (C*A*V)) =
      (fun V => coefficient β ^ as.length * halfTrace ((as.prod*(C*A))*V)) := by
    funext V
    rw [wordAverage_exact,halfTrace_mul_comm (C*A*V) as.prod]
    simp only [mul_assoc]
  rw [he]
  exact (trace_integrable β (as.prod*(C*A))).const_mul _

end OperatorDerivativeRewrite.Foundation.SU2WilsonConvolution
