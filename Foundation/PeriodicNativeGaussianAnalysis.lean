import Foundation.PeriodicCancellingRestTail
import Foundation.PeriodicGaussianTransferGram
import Mathlib.Analysis.Normed.Operator.Extend
/-! Actual Gaussian analysis in ORIGINAL native physical L2. No boundedness,
unitarity, nonlinear-product transport or full conditional-score identification. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicNativeGaussianAnalysis
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround
open PeriodicSlabL2 PeriodicPhysicalKineticReduction PeriodicGaussianTransferGram
attribute [local irreducible] boundaryHaar spatialAction temporalAction kernel

abbrev GaussianSpace := Lp ℝ 2 (FiniteGaussian.productGaussian (SpatialEdge × Fin 4))

/-- The actual vector integral exists for every Haar-L1 scalar, not only bounded scalars. -/
theorem feature_integrable (β : ℝ) (f : State → ℝ) (hf : Integrable f boundaryHaar) :
    Integrable (fun U => f U • wilsonFeature β U) boundaryHaar := by
  apply hf.norm.mono'
    (hf.aestronglyMeasurable.smul (wilsonFeature_continuous β).aestronglyMeasurable)
  filter_upwards with U
  change ‖f U • wilsonFeature β U‖ ≤ ‖f U‖
  rw [norm_smul,wilsonFeature_norm,mul_one]

/-- L1 version of the actual Wilson Gaussian Gram identity. -/
theorem haar_gram_L1 (β : ℝ) (hb : 0≤β) (f : State → ℝ) (hf : Integrable f boundaryHaar) :
    (∫ U,∫ V,Real.exp (-β*temporalAction U V 1)*(f U*f V) ∂boundaryHaar ∂boundaryHaar) =
      ‖∫ U,f U • wilsonFeature β U ∂boundaryHaar‖^2 := by
  have hi := feature_integrable β f hf
  let F := fun U => f U • wilsonFeature β U
  calc
    _ = ∫ U,∫ V,inner ℝ (F U) (F V) ∂boundaryHaar ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      apply integral_congr_ae
      filter_upwards with V
      dsimp [F]
      rw [real_inner_smul_left,inner_smul_right,wilsonFeature_inner β hb]
      ring
    _ = ∫ U,inner ℝ (F U) (∫ V,F V ∂boundaryHaar) ∂boundaryHaar := by
      apply integral_congr_ae
      filter_upwards with U
      exact integral_inner hi (F U)
    _ = inner ℝ (∫ U,F U ∂boundaryHaar) (∫ V,F V ∂boundaryHaar) := by
      calc
        _ = ∫ U,inner ℝ (∫ V,F V ∂boundaryHaar) (F U) ∂boundaryHaar :=
          integral_congr_ae (ae_of_all _ (fun U => real_inner_comm _ _))
        _ = _ := integral_inner hi _
    _ = _ := real_inner_self_eq_norm_sq _

theorem dressed_integrable {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary) :
    Integrable (fun U => PeriodicLocalGroundHarnack.dressed g U*f U) boundaryHaar := by
  have hM : Measurable (multiplier β) :=
    (((spatial_action_measurable.const_mul (-β)).div_const 2).exp)
  apply (native_weighted_integrable g f hf hm).norm.mono'
    ((hM.mul g.measurable).mul hf).aestronglyMeasurable
  filter_upwards with U
  have hM1 : multiplier β U≤1 := by
    unfold multiplier
    exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (spatial_action_bounds U).1) (by norm_num))
  change ‖(multiplier β U*g.function U)*f U‖ ≤ ‖g.function U*f U‖
  have hpos : 0<multiplier β U := Real.exp_pos _
  rw [mul_assoc,norm_mul,Real.norm_eq_abs,abs_of_pos hpos]
  exact mul_le_of_le_one_left (norm_nonneg _) hM1

/-- Original native operator pairing on arbitrary measurable L2 representatives. -/
theorem native_pairing {β : ℝ} (g : GroundData β) (f : State → ℝ)
    (hm : MemLp f 2 g.stationary) :
    inner ℝ (operator g (hm.toLp f)) (hm.toLp f) =
      ∫ U,f U*(∫ V,f V ∂g.transition U) ∂g.stationary := by
  let F := hm.toLp f
  have hL := (left_preserving g).quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp
  have hR := (right_preserving g).quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp
  have hI : Integrable (fun p : State × State => f p.1*f p.2) (edgeLaw g) := by
    apply (L2.integrable_inner (𝕜 := ℝ) (leftEmbedding g F) (rightEmbedding g F)).congr
    filter_upwards [Lp.coeFn_compMeasurePreserving F (left_preserving g),
      Lp.coeFn_compMeasurePreserving F (right_preserving g),hL,hR] with p hA hB hC hD
    change inner ℝ (leftEmbedding g F p) (rightEmbedding g F p)=f p.1*f p.2
    change leftEmbedding g F p=F p.1 at hA
    change rightEmbedding g F p=F p.2 at hB
    change F p.1=f p.1 at hC
    change F p.2=f p.2 at hD
    rw [hA,hB,hC,hD]
    simp only [RCLike.inner_apply,conj_trivial,mul_comm]
  rw [operator_pairing]
  calc
    _ = ∫ p : State × State,f p.1*f p.2 ∂edgeLaw g := by
      apply integral_congr_ae
      filter_upwards [hL,hR] with p hA hB
      change (hm.toLp f) p.1=f p.1 at hA
      change (hm.toLp f) p.2=f p.2 at hB
      rw [hA,hB]
    _ = _ := by
      rw [show edgeLaw g=g.stationary ⊗ₘ g.transition from rfl,Measure.integral_compProd hI]
      simp_rw [integral_const_mul]

theorem native_gram_L2 {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    inner ℝ (operator g (hm.toLp f)) (hm.toLp f)=
      (1/(g.value*g.normalizer))*
        ‖∫ U,(PeriodicLocalGroundHarnack.dressed g U*f U) • wilsonFeature β U ∂boundaryHaar‖^2 := by
  rw [native_pairing,g.stationary_pairing]
  have hI : pairing β (fun U => g.function U*f U) (fun U => g.function U*f U)=
      ∫ U,∫ V,Real.exp (-β*temporalAction U V 1)*
        ((PeriodicLocalGroundHarnack.dressed g U*f U)*
          (PeriodicLocalGroundHarnack.dressed g V*f V)) ∂boundaryHaar ∂boundaryHaar := by
    unfold pairing
    apply integral_congr_ae
    filter_upwards with U
    rw [invariant_transfer β U (fun V => g.function V*f V) (g.measurable.mul hf)
      (native_weighted_integrable g f hf hm) (fun a V => by rw [g.invariant,hInv])]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with V
    unfold weight halfAction PeriodicLocalGroundHarnack.dressed multiplier
    rw [show -β*(spatialAction U/2+temporalAction U V 1+spatialAction V/2)=
      -β*spatialAction U/2+-β*temporalAction U V 1+-β*spatialAction V/2 by ring]
    rw [Real.exp_add,Real.exp_add]
    ring
  rw [hI,haar_gram_L1 β hb _ (dressed_integrable hb g f hf hm)]
  ring


def rawAnalysis {β : ℝ} (g : GroundData β) (f : State → ℝ) : GaussianSpace :=
  ∫ U,(PeriodicLocalGroundHarnack.dressed g U*f U) • wilsonFeature β U ∂boundaryHaar

def analysis {β : ℝ} (g : GroundData β) (f : State → ℝ) : GaussianSpace :=
  (Real.sqrt (g.value*g.normalizer))⁻¹ • rawAnalysis g f

theorem analysis_norm_square {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    ‖analysis g f‖^2=inner ℝ (operator g (hm.toLp f)) (hm.toLp f) := by
  have hp : 0<g.value*g.normalizer := mul_pos g.value_pos g.normalizer_pos
  unfold analysis rawAnalysis
  rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs,inv_pow,Real.sq_sqrt hp.le]
  simpa only [one_div] using (native_gram_L2 hb g f hf hm hInv).symm

theorem analysis_contraction {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) :
    ‖analysis g f‖≤‖hm.toLp f‖ := by
  have hs : ‖analysis g f‖^2≤‖hm.toLp f‖^2 := by
    rw [analysis_norm_square hb g f hf hm hInv]
    calc
      _ ≤ ‖operator g (hm.toLp f)‖*‖hm.toLp f‖ := real_inner_le_norm _ _
      _ ≤ ‖hm.toLp f‖*‖hm.toLp f‖ :=
        mul_le_mul_of_nonneg_right (operator_contraction g _) (norm_nonneg _)
      _ = _ := (pow_two _).symm
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

theorem analysis_sub {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hm : MemLp f 2 g.stationary) (hn : MemLp h 2 g.stationary) :
    analysis g (f-h)=analysis g f-analysis g h := by
  have hF := feature_integrable β _ (dressed_integrable hb g f hf hm)
  have hG := feature_integrable β _ (dressed_integrable hb g h hh hn)
  have he : (fun U => (PeriodicLocalGroundHarnack.dressed g U*(f-h) U) • wilsonFeature β U)=
      (fun U => (PeriodicLocalGroundHarnack.dressed g U*f U) • wilsonFeature β U -
        (PeriodicLocalGroundHarnack.dressed g U*h U) • wilsonFeature β U) := by
    funext U
    simp only [Pi.sub_apply,mul_sub,sub_smul]
  unfold analysis rawAnalysis
  rw [he,integral_sub hF hG,smul_sub]

/-- Quotient compatibility in the ORIGINAL native measure, not an output norm. -/
theorem analysis_ae_eq {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hm : MemLp f 2 g.stationary) (hn : MemLp h 2 g.stationary)
    (hif : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (hih : ∀ a U,h (PeriodicSlabGauge.gaugeAction a U)=h U)
    (he : f=ᵐ[g.stationary] h) : analysis g f=analysis g h := by
  have hclass : hm.toLp f=hn.toLp h := (MemLp.toLp_eq_toLp_iff hm hn).mpr he
  have hi : ∀ a U,(f-h) (PeriodicSlabGauge.gaugeAction a U)=(f-h) U := by
    intro a U
    simp only [Pi.sub_apply,hif,hih]
  have hbound := analysis_contraction hb g (f-h) (hf.sub hh) (hm.sub hn) hi
  rw [analysis_sub hb g f h hf hh hm hn,MemLp.toLp_sub hm hn,hclass,sub_self,norm_zero] at hbound
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _)))

/-- Exponentially small Gaussian analysis of actual high-action physical inputs. -/
theorem bad_analysis_bound {β : ℝ} (hb : 16777216≤β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (hs : ∀ᵐ U ∂g.stationary,U∉PeriodicCancellingRestTail.bad → f U=0) :
    ‖analysis g f‖^2 ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-β)*‖hm.toLp f‖^2 := by
  have hhigh := PeriodicHighActionL2.native_high_action_L2 hb g f hf hm hInv β (by
    filter_upwards [hs] with U hU
    intro hA
    apply hU
    intro hbad
    have hS := PeriodicCancellingRestTail.bad_action U hbad
    have hβ : 0<β := by linarith
    nlinarith)
  rw [analysis_norm_square (by linarith) g f hf hm hInv]
  exact (le_abs_self _).trans hhigh

theorem bad_gaussian_pairing_bound {β : ℝ} (hb : 16777216≤β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hInv : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U)
    (hs : ∀ᵐ U ∂g.stationary,U∉PeriodicCancellingRestTail.bad → f U=0) (Z : GaussianSpace) :
    |inner ℝ Z (analysis g f)|^2 ≤
      ‖Z‖^2*((PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-β)*‖hm.toLp f‖^2) := by
  have hc : |inner ℝ Z (analysis g f)|≤‖Z‖*‖analysis g f‖ := by
    simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) Z (analysis g f)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hc
  rw [mul_pow] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_left (bad_analysis_bound hb g f hf hm hInv hs) (sq_nonneg _))


theorem analysis_add {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f h : State → ℝ) (hf : Measurable f) (hh : Measurable h)
    (hm : MemLp f 2 g.stationary) (hn : MemLp h 2 g.stationary) :
    analysis g (f+h)=analysis g f+analysis g h := by
  have hF := feature_integrable β _ (dressed_integrable hb g f hf hm)
  have hG := feature_integrable β _ (dressed_integrable hb g h hh hn)
  have he : (fun U => (PeriodicLocalGroundHarnack.dressed g U*(f+h) U) • wilsonFeature β U)=
      (fun U => (PeriodicLocalGroundHarnack.dressed g U*f U) • wilsonFeature β U +
        (PeriodicLocalGroundHarnack.dressed g U*h U) • wilsonFeature β U) := by
    funext U
    simp only [Pi.add_apply,mul_add,add_smul]
  unfold analysis rawAnalysis
  rw [he,integral_add hF hG,smul_add]

theorem analysis_smul {β : ℝ} (hb : 0≤β) (g : GroundData β)
    (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary) (c : ℝ) :
    analysis g (c • f)=c • analysis g f := by
  have he : (fun U => (PeriodicLocalGroundHarnack.dressed g U*(c • f) U) • wilsonFeature β U)=
      (fun U => c • ((PeriodicLocalGroundHarnack.dressed g U*f U) • wilsonFeature β U)) := by
    funext U
    simp only [Pi.smul_apply,smul_eq_mul,smul_smul]
    congr 1
    ring
  unfold analysis rawAnalysis
  rw [he,integral_smul,smul_comm]

abbrev Core {β : ℝ} (g : GroundData β) (K : ℝ) := PeriodicHighActionL2.represented g K
abbrev Completed {β : ℝ} (g : GroundData β) (K : ℝ) := PeriodicHighActionL2.completed g K

private theorem rep_exists {β : ℝ} (g : GroundData β) (K : ℝ) (F : Core g K) :
    ∃ f : State → ℝ,Measurable f ∧ ∃ hm : MemLp f 2 g.stationary,
      (∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) ∧
      (∀ᵐ U ∂g.stationary,β*spatialAction U≤K → f U=0) ∧ hm.toLp f=F.val := F.property

private def rep {β : ℝ} (g : GroundData β) (K : ℝ) (F : Core g K) : State → ℝ :=
  Classical.choose (rep_exists g K F)
private theorem rep_spec {β : ℝ} (g : GroundData β) (K : ℝ) (F : Core g K) :
    Measurable (rep g K F) ∧ ∃ hm : MemLp (rep g K F) 2 g.stationary,
      (∀ a U,rep g K F (PeriodicSlabGauge.gaugeAction a U)=rep g K F U) ∧
      (∀ᵐ U ∂g.stationary,β*spatialAction U≤K → rep g K F U=0) ∧
        hm.toLp (rep g K F)=F.val := Classical.choose_spec (rep_exists g K F)
private def repMem {β : ℝ} (g : GroundData β) (K : ℝ) (F : Core g K) :
    MemLp (rep g K F) 2 g.stationary := Classical.choose (rep_spec g K F).2
private theorem rep_data {β : ℝ} (g : GroundData β) (K : ℝ) (F : Core g K) :
    (∀ a U,rep g K F (PeriodicSlabGauge.gaugeAction a U)=rep g K F U) ∧
    (∀ᵐ U ∂g.stationary,β*spatialAction U≤K → rep g K F U=0) ∧
      (repMem g K F).toLp (rep g K F)=F.val := Classical.choose_spec (rep_spec g K F).2

/-- Gaussian analysis on the represented core, with its ORIGINAL native norm. -/
def coreAnalysis {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ) : Core g K →ₗ[ℝ] GaussianSpace where
  toFun F := analysis g (rep g K F)
  map_add' F G := by
    let f := rep g K F
    let h := rep g K G
    have hf := (rep_spec g K F).1
    have hh := (rep_spec g K G).1
    have hm := repMem g K F
    have hn := repMem g K G
    have hi : ∀ a U,(f+h) (PeriodicSlabGauge.gaugeAction a U)=(f+h) U := by
      intro a U
      change rep g K F (PeriodicSlabGauge.gaugeAction a U)+
        rep g K G (PeriodicSlabGauge.gaugeAction a U)=rep g K F U+rep g K G U
      rw [(rep_data g K F).1,(rep_data g K G).1]
    have he : (repMem g K (F+G)).toLp (rep g K (F+G))=(hm.add hn).toLp (f+h) := by
      rw [(rep_data g K (F+G)).2.2,MemLp.toLp_add hm hn,
        (rep_data g K F).2.2,(rep_data g K G).2.2]
      rfl
    have ha := analysis_ae_eq hb g (rep g K (F+G)) (f+h) (rep_spec g K (F+G)).1
      (hf.add hh) (repMem g K (F+G)) (hm.add hn) (rep_data g K (F+G)).1 hi
      ((MemLp.toLp_eq_toLp_iff _ _).mp he)
    exact ha.trans (analysis_add hb g f h hf hh hm hn)
  map_smul' c F := by
    have hm := repMem g K F
    have hi : ∀ a U,(c • rep g K F) (PeriodicSlabGauge.gaugeAction a U)=(c • rep g K F) U := by
      intro a U
      simp only [Pi.smul_apply,(rep_data g K F).1]
    have he : (repMem g K (c • F)).toLp (rep g K (c • F))=
        (hm.const_smul c).toLp (c • rep g K F) := by
      rw [(rep_data g K (c • F)).2.2,MemLp.toLp_const_smul c hm,(rep_data g K F).2.2]
      rfl
    have ha := analysis_ae_eq hb g (rep g K (c • F)) (c • rep g K F) (rep_spec g K (c • F)).1
      ((rep_spec g K F).1.const_smul c) (repMem g K (c • F)) (hm.const_smul c)
      (rep_data g K (c • F)).1 hi ((MemLp.toLp_eq_toLp_iff _ _).mp he)
    exact ha.trans (analysis_smul hb g _ (rep_spec g K F).1 hm c)

theorem coreAnalysis_bound {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ) (F : Core g K) :
    ‖coreAnalysis hb g K F‖≤‖F‖ := by
  have h := analysis_contraction hb g _ (rep_spec g K F).1 (repMem g K F) (rep_data g K F).1
  rw [(rep_data g K F).2.2] at h
  exact h

/-- Agreement with every admissible original native representative. -/
theorem coreAnalysis_of_representative {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ)
    (F : Core g K) (f : State → ℝ) (hf : Measurable f) (hm : MemLp f 2 g.stationary)
    (hi : ∀ a U,f (PeriodicSlabGauge.gaugeAction a U)=f U) (he : hm.toLp f=F.val) :
    coreAnalysis hb g K F=analysis g f := by
  exact analysis_ae_eq hb g _ f (rep_spec g K F).1 hf (repMem g K F) hm
    (rep_data g K F).1 hi ((MemLp.toLp_eq_toLp_iff _ _).mp ((rep_data g K F).2.2.trans he.symm))

def coreInclusion {β : ℝ} (g : GroundData β) (K : ℝ) : Core g K →ₗ[ℝ] Completed g K where
  toFun F := ⟨F.val,(PeriodicHighActionL2.represented g K).le_topologicalClosure F.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coreInclusion_dense {β : ℝ} (g : GroundData β) (K : ℝ) : DenseRange (coreInclusion g K) := by
  exact (denseRange_inclusion_iff
    (show (PeriodicHighActionL2.represented g K : Set (StateL2 g)) ⊆
      closure (PeriodicHighActionL2.represented g K : Set (StateL2 g)) from subset_closure)).mpr subset_rfl

/-- Actual bounded extension to the EXISTING closed native physical high space. -/
def completedAnalysis {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ) :
    Completed g K →L[ℝ] GaussianSpace :=
  (coreAnalysis hb g K).extendOfNorm (coreInclusion g K)

theorem completedAnalysis_core {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ) (F : Core g K) :
    completedAnalysis hb g K (coreInclusion g K F)=coreAnalysis hb g K F := by
  exact LinearMap.extendOfNorm_eq (coreInclusion_dense g K)
    ⟨1,fun F => by
      change ‖coreAnalysis hb g K F‖≤1*‖F‖
      simpa only [one_mul] using coreAnalysis_bound hb g K F⟩ F

theorem completedAnalysis_contraction {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ)
    (F : Completed g K) : ‖completedAnalysis hb g K F‖≤‖F‖ := by
  simpa only [completedAnalysis,one_mul] using LinearMap.norm_extendOfNorm_apply_le
    (f := coreAnalysis hb g K) (coreInclusion_dense g K) 1
    (fun F => by
      change ‖coreAnalysis hb g K F‖≤1*‖F‖
      simpa only [one_mul] using coreAnalysis_bound hb g K F) F

theorem completedAnalysis_gram {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ)
    (F : Completed g K) : ‖completedAnalysis hb g K F‖^2=
      inner ℝ (operator g F.val) F.val := by
  have hc : IsClosed {F : Completed g K | ‖completedAnalysis hb g K F‖^2=
      inner ℝ (operator g F.val) F.val} :=
    isClosed_eq ((completedAnalysis hb g K).continuous.norm.pow 2)
      (((operator g).continuous.comp continuous_subtype_val).inner (𝕜 := ℝ) continuous_subtype_val)
  refine isClosed_property (coreInclusion_dense g K) hc ?_ F
  intro G
  rw [completedAnalysis_core]
  change ‖analysis g (rep g K G)‖^2=inner ℝ (operator g G.val) G.val
  rw [analysis_norm_square hb g _ (rep_spec g K G).1 (repMem g K G) (rep_data g K G).1,
    (rep_data g K G).2.2]


theorem completedAnalysis_pairing {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ)
    (F G : Completed g K) : inner ℝ (completedAnalysis hb g K F) (completedAnalysis hb g K G)=
      inner ℝ (operator g F.val) G.val := by
  have h := completedAnalysis_gram hb g K (F+G)
  rw [map_add,norm_add_sq_real] at h
  change ‖completedAnalysis hb g K F‖^2 + 2 * inner ℝ (completedAnalysis hb g K F) (completedAnalysis hb g K G) + ‖completedAnalysis hb g K G‖^2 = _ at h
  change _ = inner ℝ (operator g (F.val+G.val)) (F.val+G.val) at h
  rw [map_add,inner_add_left,inner_add_right,inner_add_right] at h
  rw [completedAnalysis_gram hb g K F,completedAnalysis_gram hb g K G] at h
  have hs : inner ℝ (operator g G.val) F.val=inner ℝ (operator g F.val) G.val := by
    rw [operator_symmetric,real_inner_comm]
  rw [hs] at h
  linarith

/-- Exact Gram factorization of the ORIGINAL compressed Wilson transfer. -/
theorem completedAnalysis_adjoint_comp {β : ℝ} (hb : 0≤β) (g : GroundData β) (K : ℝ) :
    (completedAnalysis hb g K).adjoint.comp (completedAnalysis hb g K)=
      PeriodicHighActionL2.compression g K := by
  apply ContinuousLinearMap.ext
  intro F
  apply ext_inner_right ℝ
  intro G
  change inner ℝ ((completedAnalysis hb g K).adjoint (completedAnalysis hb g K F)) G = _
  rw [(completedAnalysis hb g K).adjoint_inner_left,
    completedAnalysis_pairing,PeriodicHighActionL2.compression_pairing]

theorem completedAnalysis_high_bound {β : ℝ} (hb : 16777216≤β) (g : GroundData β) (K : ℝ)
    (F : Completed g K) : ‖completedAnalysis (by linarith) g K F‖^2 ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-K)*‖F‖^2 := by
  rw [completedAnalysis_gram]
  exact (le_abs_self _).trans (PeriodicHighActionL2.completed_bound hb g K F.val F.property)

/-- Squared operator norm retained in the original native completion. -/
theorem completedAnalysis_norm_square {β : ℝ} (hb : 16777216≤β) (g : GroundData β) (K : ℝ) :
    ‖completedAnalysis (by linarith) g K‖^2 ≤
      (PeriodicGroundHaarScale.upperConstant/PeriodicGaugeSaturatedGround.eigenLowerConstant)*
        Real.exp (-K) := by
  have h := ContinuousLinearMap.norm_adjoint_comp_self (completedAnalysis (by linarith) g K)
  rw [completedAnalysis_adjoint_comp] at h
  calc
    _ = ‖PeriodicHighActionL2.compression g K‖ := by nlinarith [h]
    _ ≤ _ := PeriodicHighActionL2.compression_norm hb g K

end OperatorDerivativeRewrite.Foundation.PeriodicNativeGaussianAnalysis
