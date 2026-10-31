import Foundation.PeriodicPlaquetteNoise

/-! Actual local plaquettes fail to be a full-family asymptotic quasimode.
The actual half-coupling eigenvalue ratio bounds the stationary energy second
moment. A polynomial eigenvalue lower bound forces bounded ratios at arbitrarily
large couplings, without a uniform doubling assumption. The proved transition
noise floor then gives a positive native residual/Rayleigh loss at those scales.
Actual normalized one-step edge correlation cannot converge to one. The theorem
does not give a lower loss at every large coupling, a full spectral gap, bounded
correlation time, or a continuum or infinite-volume physical mass gap. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicSlabJoint PeriodicTemporalConcentration PeriodicTransferVariation
namespace OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteScaleObstruction
attribute [local irreducible] boundaryHaar gaugeHaar kernel tripleLaw PeriodicSlabJoint.reference

theorem scalar_energy_comparison (β x : ℝ) (hb : 0 < β) (hx : 0 ≤ x) :
    x^2*Real.exp (-β*x) ≤ (8/β^2)*Real.exp (-(β/2)*x) := by
  have hy : 0 ≤ β*x/2 := by positivity
  have hs := Real.sum_le_exp_of_nonneg hy 3
  norm_num [Finset.sum_range_succ,Nat.factorial] at hs
  have hq : β^2*x^2/8 ≤ Real.exp (β*x/2) := by nlinarith
  have h := mul_le_mul_of_nonneg_right hq
    (show 0 ≤ (8/β^2)*Real.exp (-β*x) by positivity)
  have heL : (β^2*x^2/8)*((8/β^2)*Real.exp (-β*x))=x^2*Real.exp (-β*x) := by
    field_simp [hb.ne']
  have heR : Real.exp (β*x/2)*((8/β^2)*Real.exp (-β*x))=
      (8/β^2)*Real.exp (-(β/2)*x) := by
    rw [show Real.exp (β*x/2)*((8/β^2)*Real.exp (-β*x))=
      (8/β^2)*(Real.exp (β*x/2)*Real.exp (-β*x)) by ring,← Real.exp_add]
    congr 2
    ring
  rw [heL,heR] at h
  exact h

theorem stationary_quadratic_le (α : ℝ) (g : GroundData α) (f : State → ℝ)
    (hf : Measurable f) (B : ℝ) (hb : ∀ U,|f U| ≤ B) :
    (∫ U,f U*(∫ V,f V ∂g.transition U) ∂g.stationary) ≤ ∫ U,f U^2 ∂g.stationary := by
  have hmem : MemLp f 2 g.stationary := MemLp.of_bound hf.aestronglyMeasurable B
    (ae_of_all _ (fun U => by simpa only [Real.norm_eq_abs] using hb U))
  have hp := transfer_memLp g f hf B hb
  let F := hmem.toLp f
  have he : inner ℝ (operator g F) F=∫ U,f U*transfer g f U ∂g.stationary := by
    change inner ℝ (operator g (hmem.toLp f)) (hmem.toLp f)=_
    rw [operator_toLp g f hmem hf B hb,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hp,MemLp.coeFn_toLp hmem] with U hP hF
    rw [hP,hF]
    rfl
  have h := (real_inner_le_norm (operator g F) F).trans
    (mul_le_mul_of_nonneg_right (operator_contraction g F) (norm_nonneg F))
  rw [he,← pow_two] at h
  change (∫ U,f U*transfer g f U ∂g.stationary) ≤ ‖hmem.toLp f‖^2 at h
  rw [state_norm_square] at h
  exact h

theorem cross_ground_quadratic_upper (α β : ℝ) (g : GroundData α) (h : GroundData β) :
    pairing α h.function h.function ≤ g.value*h.normalizer := by
  let f : State → ℝ := fun U => h.function U/g.function U
  have hf : Measurable f := h.measurable.div g.measurable
  have hb (U : State) : |f U| ≤ |h.upper|/g.lower := by
    dsimp [f]
    rw [abs_div,abs_of_pos (g.function_pos U)]
    exact (div_le_div_of_nonneg_right ((h.bounds U).2.trans (le_abs_self _)) (g.function_pos U).le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) g.lower_pos (g.bounds U).1)
  have hq := stationary_quadratic_le α g f hf (|h.upper|/g.lower) hb
  rw [g.stationary_pairing f f] at hq
  have he : (fun U => g.function U*f U)=h.function := by
    funext U
    dsimp [f]
    field_simp [(g.function_pos U).ne']
  rw [he,g.stationary_integral] at hq
  have hi : (∫ U,g.function U^2*f U^2 ∂boundaryHaar)=h.normalizer := by
    unfold GroundData.normalizer
    apply integral_congr_ae
    filter_upwards with U
    dsimp [f]
    field_simp [(g.function_pos U).ne']
  rw [hi] at hq
  have hq' := (div_le_iff₀ (mul_pos g.value_pos g.normalizer_pos)).mp hq
  calc
    _ ≤ (h.normalizer/g.normalizer)*(g.value*g.normalizer) := hq'
    _ = _ := by field_simp [g.normalizer_pos.ne']


def crossWeight (α β : ℝ) (h : GroundData β) (q : Triple) : ℝ :=
  weight α q.1.1 q.1.2 q.2*(h.function q.1.1*h.function q.1.2)

theorem cross_weight_integrable (α β : ℝ) (h : GroundData β) :
    Integrable (crossWeight α β h) PeriodicSlabJoint.reference := by
  have hm : Measurable (crossWeight α β h) := (weight_joint_measurable α).mul
    ((h.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (h.measurable.comp (measurable_snd.comp measurable_fst)))
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp (768*|α|)*(|h.upper| * |h.upper|))
  filter_upwards with q
  change |weight α q.1.1 q.1.2 q.2*(h.function q.1.1*h.function q.1.2)| ≤ _
  rw [abs_mul,abs_of_pos (by unfold weight; exact Real.exp_pos _ : 0 < weight α q.1.1 q.1.2 q.2),abs_mul]
  exact mul_le_mul (weight_bounds α q.1.1 q.1.2 q.2).2
    (mul_le_mul ((h.bounds q.1.1).2.trans (le_abs_self _)) ((h.bounds q.1.2).2.trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)) (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (Real.exp_pos _).le

theorem cross_weight_pairing (α β : ℝ) (h : GroundData β) :
    (∫ q,crossWeight α β h q ∂PeriodicSlabJoint.reference)=pairing α h.function h.function := by
  have hi := cross_weight_integrable α β h
  rw [PeriodicSlabJoint.reference] at hi
  have hrow (UV : State × State) : (∫ a,crossWeight α β h (UV,a) ∂gaugeHaar)=
      kernel α UV.1 UV.2*(h.function UV.1*h.function UV.2) := by
    dsimp only [crossWeight]
    rw [integral_mul_const]
    unfold kernel
    rfl
  have hj : Integrable (fun UV : State × State => kernel α UV.1 UV.2*(h.function UV.1*h.function UV.2))
      (boundaryHaar.prod boundaryHaar) := hi.integral_prod_left.congr (ae_of_all _ hrow)
  rw [PeriodicSlabJoint.reference,integral_prod _ hi]
  simp_rw [hrow]
  rw [integral_prod _ hj]
  unfold pairing
  apply integral_congr_ae
  filter_upwards with U
  have he (V : State) : kernel α U V*(h.function U*h.function V)=h.function U*(kernel α U V*h.function V) := by ring
  simp_rw [he,integral_const_mul]

theorem energy_square_scale_bound (β : ℝ) (hb : 0 < β) (h : GroundData β) (g : GroundData (β/2)) :
    (∫ q,energy q^2 ∂tripleLaw h) ≤ (8/β^2)*(g.value/h.value) := by
  have hp (q : Triple) : jointWeight h q*energy q^2 ≤ (8/β^2)*crossWeight (β/2) β h q := by
    have hs := mul_le_mul_of_nonneg_right (scalar_energy_comparison β (energy q) hb (energy_bounds q).1)
      (mul_pos (h.function_pos q.1.1) (h.function_pos q.1.2)).le
    convert hs using 1 <;> simp only [jointWeight,crossWeight,weight,energy] <;> ring
  have hi := integral_mono_of_nonneg (μ := PeriodicSlabJoint.reference)
    (ae_of_all _ (fun q => mul_nonneg (PeriodicSlabJoint.weight_pos h q).le (sq_nonneg (energy q))))
    ((cross_weight_integrable (β/2) β h).const_mul (8/β^2)) (ae_of_all _ hp)
  rw [integral_const_mul,cross_weight_pairing] at hi
  have hmax := mul_le_mul_of_nonneg_left (cross_ground_quadratic_upper (β/2) β g h)
    (show 0 ≤ 8/β^2 by positivity)
  have hd := div_le_div_of_nonneg_right (hi.trans hmax) (mul_pos h.value_pos h.normalizer_pos).le
  rw [PeriodicSlabJoint.integral_formula]
  calc
    _ ≤ ((8/β^2)*(g.value*h.normalizer))/(h.value*h.normalizer) := hd
    _ = _ := by field_simp [h.value_pos.ne',h.normalizer_pos.ne']


open Filter
open scoped Topology
private theorem no_lower_halving (u : ℕ → ℝ) (C : ℝ) (hC : 0 < C)
    (hl : ∀ n,C ≤ u n) (hs : ∀ n,u (n+1) ≤ (1/2)*u n) : False := by
  have hu (n : ℕ) : u n ≤ (1/2)^n*u 0 :=
    le_geom (by norm_num : (0:ℝ) ≤ 1/2) n (fun k _ => hs k)
  have ht : Tendsto (fun n : ℕ => (1/2:ℝ)^n*u 0) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_const (u 0)
  have h : C ≤ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Eventually.of_forall (fun n => (hl n).trans (hu n)))
  linarith

theorem polynomial_good_scale (F : ℝ → ℝ) (m : ℕ) (C : ℝ) (hC : 0 < C)
    (hF : ∀ b : ℝ,1 ≤ b → C/b^m ≤ F b) (B : ℝ) :
    ∃ b : ℝ,B ≤ b ∧ 1 ≤ b ∧ F (b/2) ≤ (2*(2:ℝ)^m)*F b := by
  by_contra hh
  push Not at hh
  let b : ℝ := max B 1
  have hb : 1 ≤ b := le_max_right _ _
  have hB : B ≤ b := le_max_left _ _
  let s : ℕ → ℝ := fun n => (2:ℝ)^n*b
  have hs (n : ℕ) : b ≤ s n := by
    exact le_mul_of_one_le_left (by linarith : 0 ≤ b) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  have hs1 (n : ℕ) : 1 ≤ s n := hb.trans (hs n)
  have hsp (n : ℕ) : 0 < s n := lt_of_lt_of_le zero_lt_one (hs1 n)
  have hss (n : ℕ) : s (n+1)=2*s n := by dsimp [s]; rw [pow_succ]; ring
  have hhalf (n : ℕ) : s (n+1)/2=s n := by rw [hss]; ring
  let u : ℕ → ℝ := fun n => s n^m*F (s n)
  have hl (n : ℕ) : C ≤ u n := by
    have h := (div_le_iff₀ (pow_pos (hsp n) m)).mp (hF (s n) (hs1 n))
    simpa only [u,mul_comm] using h
  have hu (n : ℕ) : u (n+1) ≤ (1/2)*u n := by
    have h := (hh (s (n+1)) (hB.trans (hs (n+1))) (hs1 (n+1))).le
    rw [hhalf] at h
    have hp := mul_le_mul_of_nonneg_left h (pow_nonneg (hsp n).le m)
    have hps : s (n+1)^m=(2:ℝ)^m*s n^m := by rw [hss,mul_pow]
    dsimp only [u]
    rw [hps]
    nlinarith [hp]
  exact no_lower_halving u C hC hl hu


open QuaternionSU2Representation PeriodicCurvatureVariance PeriodicCurvatureTransfer PeriodicPlaquetteNoise
def scaleConstant : ℝ := 2*(2:ℝ)^384
def nativeFloor : ℝ := 3/(76832*scaleConstant)
theorem scaleConstant_pos : 0 < scaleConstant := by unfold scaleConstant; positivity
theorem nativeFloor_pos : 0 < nativeFloor := by unfold nativeFloor; exact div_pos (by norm_num) (mul_pos (by norm_num) scaleConstant_pos)

theorem actual_good_scale (B : ℝ) : ∃ β : ℝ,B ≤ β ∧ 1 ≤ β ∧
    (ground (β/2)).value ≤ scaleConstant*(ground β).value := by
  exact polynomial_good_scale (fun β => (ground β).value) 384
    PeriodicPolynomialGround.lowerConstant PeriodicPolynomialGround.lowerConstant_pos
    (fun β hb => PeriodicPolynomialGround.eigenvalue_beta (ground β) hb) B

theorem variance_ratio_at_good_scale (β : ℝ) (hb : 1 ≤ β) (h : GroundData β)
    (g : GroundData (β/2)) (p : SpatialFace) (K : ℝ) (hK : 0 < K)
    (hr : g.value ≤ K*h.value) :
    3/(76832*K) ≤ (6/(49*(1+6*β)^2))/(2*variance (plaquette p) h.stationary) := by
  have hβ : 0 < β := by linarith
  have hm := (energy_square_scale_bound β hβ h g).trans
    (mul_le_mul_of_nonneg_left ((div_le_iff₀ h.value_pos).mpr hr) (show 0 ≤ 8/β^2 by positivity))
  have hv : variance (plaquette p) h.stationary ≤ 32*K/β^2 := by
    calc
      _ ≤ 4*((8/β^2)*K) := (variance_bound_square β h p).trans
        (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 4))
      _ = _ := by ring
  have hs : (1+6*β)^2 ≤ 49*β^2 := by
    have hp := mul_nonneg (sub_nonneg.mpr hb) (show 0 ≤ 13*β+1 by linarith)
    nlinarith [hp]
  have hc : 6/(2401*β^2) ≤ 6/(49*(1+6*β)^2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2401*β^2) (by positivity : 0 < 49*(1+6*β)^2)).mpr
    nlinarith [hs]
  have hnum := div_le_div_of_nonneg_right hc (mul_pos (by norm_num : (0:ℝ) < 2) (variance_pos h p)).le
  have hden := div_le_div_of_nonneg_left (show 0 ≤ 6/(2401*β^2) by positivity)
    (mul_pos (by norm_num : (0:ℝ) < 2) (variance_pos h p))
    (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 2))
  have he : (6/(2401*β^2))/(2*(32*K/β^2))=3/(76832*K) := by
    field_simp [hβ.ne',hK.ne']
    norm_num
  rw [he] at hden
  exact hden.trans hnum

theorem actual_large_native_loss (p : SpatialFace) (B : ℝ) :
    ∃ β : ℝ,B ≤ β ∧ 1 ≤ β ∧
      nativeFloor ≤ ‖operator (ground β) (normalized (ground β) p)-normalized (ground β) p‖ ∧
      nativeFloor ≤ SelfAdjointContractionIteration.dissipation (operator (ground β)) (normalized (ground β) p) := by
  obtain ⟨β,hB,hb,hr⟩ := actual_good_scale B
  have h := variance_ratio_at_good_scale β hb (ground β) (ground (β/2)) p
    scaleConstant scaleConstant_pos hr
  have hβ : 0 ≤ β := by linarith
  exact ⟨β,hB,hb,h.trans (normalized_residual_lower β hβ (ground β) p),
    h.trans (normalized_dirichlet_lower β hβ (ground β) p)⟩

theorem actual_residual_not_zero (p : SpatialFace) :
    ¬Tendsto (fun β : ℝ => ‖operator (ground β) (normalized (ground β) p)-normalized (ground β) p‖)
      atTop (𝓝 0) := by
  intro h
  obtain ⟨B,hB⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds nativeFloor_pos))
  obtain ⟨β,hβ,_,hr,_⟩ := actual_large_native_loss p B
  exact not_lt_of_ge hr (hB β hβ)

theorem actual_correlation_not_one (p : SpatialFace) :
    ¬Tendsto (fun β : ℝ => inner ℝ (operator (ground β) (normalized (ground β) p))
      (normalized (ground β) p)) atTop (𝓝 1) := by
  intro h
  have hd : Tendsto (fun β : ℝ => SelfAdjointContractionIteration.dissipation
      (operator (ground β)) (normalized (ground β) p)) atTop (𝓝 0) := by
    have ht : Tendsto (fun β : ℝ => (1:ℝ)-inner ℝ
        (operator (ground β) (normalized (ground β) p)) (normalized (ground β) p)) atTop (𝓝 (1-1)) :=
      tendsto_const_nhds.sub h
    convert ht using 1
    · funext β
      unfold SelfAdjointContractionIteration.dissipation
      rw [real_inner_self_eq_norm_sq,normalized_norm]
      norm_num
    · norm_num
  obtain ⟨B,hB⟩ := eventually_atTop.mp (hd.eventually (gt_mem_nhds nativeFloor_pos))
  obtain ⟨β,hβ,_,_,hr⟩ := actual_large_native_loss p B
  exact not_lt_of_ge hr (hB β hβ)


theorem actual_edge_correlation_not_one (p : SpatialFace) :
    ¬Tendsto (fun β : ℝ => ∫ q : State × State,
      normalized (ground β) p q.1*normalized (ground β) p q.2 ∂edgeLaw (ground β)) atTop (𝓝 1) := by
  simpa only [operator_pairing] using actual_correlation_not_one p

theorem actual_large_all_plaquettes (B : ℝ) : ∃ β : ℝ,B ≤ β ∧ 1 ≤ β ∧
    ∀ p : SpatialFace,
      nativeFloor ≤ ‖operator (ground β) (normalized (ground β) p)-normalized (ground β) p‖ ∧
      nativeFloor ≤ SelfAdjointContractionIteration.dissipation (operator (ground β)) (normalized (ground β) p) := by
  obtain ⟨β,hB,hb,hr⟩ := actual_good_scale B
  refine ⟨β,hB,hb,?_⟩
  intro p
  have h := variance_ratio_at_good_scale β hb (ground β) (ground (β/2)) p
    scaleConstant scaleConstant_pos hr
  have hβ : 0 ≤ β := by linarith
  exact ⟨h.trans (normalized_residual_lower β hβ (ground β) p),
    h.trans (normalized_dirichlet_lower β hβ (ground β) p)⟩

end OperatorDerivativeRewrite.Foundation.PeriodicPlaquetteScaleObstruction
