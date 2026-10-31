import Foundation.FourCubeThermalScore
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
/-! Actual Wilson conditional laws realized by their positive square-root Haar densities.
The common Hilbert space is product-Haar L2. No Gaussian source law, arbitrary
unitary intertwiner or multiblock contraction is presumed. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace OperatorDerivativeRewrite.Foundation.FourCubeHaarHalfDensity
open FourCubeConditionalScore FourCubeHaarContinuousIntegral FourCubeBoundarySmoothAction
open FourCubeHaarParity
attribute [local irreducible] action haarIntegral

def root (β : ℝ) (a : Parameters) : Observables :=
  NormedSpace.exp (((-β/2) • action a)+(potential β a/2) • (1:Observables))

theorem root_apply (β : ℝ) (a : Parameters) (s : InteriorState) :
    root β a s=Real.exp ((-β*action a s+potential β a)/2) := by
  rw [root,exp_apply]
  simp only [ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.one_apply,smul_eq_mul,mul_one]
  congr 1
  ring

theorem root_pos (β : ℝ) (a : Parameters) (s : InteriorState) : 0<root β a s := by
  rw [root_apply]
  exact Real.exp_pos _

theorem root_sq (β : ℝ) (a : Parameters) (s : InteriorState) :
    (root β a s)^2=Real.exp (-β*action a s)/FourCubeBoundarySmoothPartition.partition β a := by
  rw [root_apply,pow_two,← Real.exp_add]
  rw [show (-β*action a s+potential β a)/2+(-β*action a s+potential β a)/2=
    -β*action a s+potential β a by ring,Real.exp_add,potential,Real.exp_neg,
    Real.exp_log (partition_pos β a)]
  rfl

/-- Actual weighted native inner products agree on the stated continuous core. -/
theorem weighted_core_inner (β : ℝ) (a : Parameters) (f g : Observables) :
    inner ℝ (ContinuousMap.toLp 2 interiorHaar ℝ (root β a*f))
      (ContinuousMap.toLp 2 interiorHaar ℝ (root β a*g))=
      inner ℝ (ContinuousMap.toLp 2 (law β a) ℝ f) (ContinuousMap.toLp 2 (law β a) ℝ g) := by
  rw [ContinuousMap.inner_toLp,ContinuousMap.inner_toLp]
  simp only [starRingEnd_apply,star_trivial]
  change (∫ s,(root β a*g) s*(root β a*f) s ∂interiorHaar)=∫ s,(g*f) s ∂law β a
  rw [law_integral,expectation,haarIntegral_apply,← integral_div]
  apply integral_congr_ae
  filter_upwards with s
  simp only [ContinuousMap.mul_apply]
  calc
    _ = g s*f s*(root β a s)^2 := by ring
    _ = _ := by rw [root_sq,weight_apply,action_apply]; ring

abbrev HaarSpace := Lp ℝ 2 interiorHaar

def rootClass (β : ℝ) (a : Parameters) : HaarSpace :=
  ContinuousMap.toLp 2 interiorHaar ℝ (root β a)

theorem rootClass_norm_square (β : ℝ) (a : Parameters) : ‖rootClass β a‖^2=1 := by
  calc
    _ = inner ℝ (rootClass β a) (rootClass β a) := (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ (ContinuousMap.toLp 2 (law β a) ℝ (1:Observables))
        (ContinuousMap.toLp 2 (law β a) ℝ (1:Observables)) := by
      simpa only [rootClass,mul_one] using weighted_core_inner β a 1 1
    _ = 1 := by rw [ContinuousMap.inner_toLp]; simp

def rootTangent (β : ℝ) (a u : Parameters) : HaarSpace :=
  (1/2:ℝ) • ContinuousMap.toLp 2 interiorHaar ℝ (root β a*score β a u)

theorem rootTangent_norm_square (β : ℝ) (a u : Parameters) :
    ‖rootTangent β a u‖^2=(1/4:ℝ)*‖nativeScore β a u‖^2 := by
  have hn : ‖ContinuousMap.toLp 2 interiorHaar ℝ (root β a*score β a u)‖^2=
      ‖nativeScore β a u‖^2 := by
    simpa only [real_inner_self_eq_norm_sq,nativeScore] using weighted_core_inner β a (score β a u) (score β a u)
  rw [rootTangent,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow,hn]
  ring

/-- The actual Banach-space derivative, before passing to Haar L2. -/
theorem root_hasDerivAt (β : ℝ) (a u : Parameters) :
    HasDerivAt (fun h : ℝ => root β (a+h • u)) ((1/2:ℝ) • (root β a*score β a u)) 0 := by
  have hl : HasDerivAt (fun h : ℝ => a+h • u) u 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const u |>.const_add a
  have hA := (action_contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt 0 hl
  have hP := ((potential_hasDerivAt β a u).div_const 2).smul_const (1:Observables)
  have he := (hasFDerivAt_exp (𝕂 := ℝ)).comp_hasDerivAt 0 ((hA.const_smul (-β/2)).add hP)
  simp only [Function.comp_def,Pi.add_apply,Pi.smul_apply,zero_smul,add_zero,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.one_apply,smul_eq_mul] at he
  convert he using 1
  · rfl
  · ext s
    simp only [root,score,ContinuousMap.mul_apply,ContinuousMap.smul_apply,
      ContinuousMap.sub_apply,ContinuousMap.const_apply,ContinuousMap.add_apply,ContinuousMap.one_apply,
      smul_eq_mul,exp_apply,actionDirection]
    ring

/-- Common-Haar strong Hilbert derivative, not merely a weak test pairing. -/
theorem rootClass_hasDerivAt (β : ℝ) (a u : Parameters) :
    HasDerivAt (fun h : ℝ => rootClass β (a+h • u)) (rootTangent β a u) 0 := by
  have h := (ContinuousMap.toLp 2 interiorHaar ℝ).hasFDerivAt.comp_hasDerivAt 0 (root_hasDerivAt β a u)
  simpa only [Function.comp_def,map_smul,rootClass,rootTangent] using h

/-- The square is exactly the density of the actual normalized conditional probability measure. -/
theorem law_root_density (β : ℝ) (a : Parameters) :
    law β a=interiorHaar.withDensity (fun s => ENNReal.ofReal ((root β a s)^2)) := by
  have hZ : BoundedExponentialTiltResponse.partition interiorHaar (source a) (144*β)=
      FourCubeBoundarySmoothPartition.partition β a := by
    unfold BoundedExponentialTiltResponse.partition BoundedExponentialTiltResponse.weighted
    change (∫ s,1*Real.exp ((144*β)*source a s) ∂interiorHaar)=haarIntegral (weight β a)
    rw [haarIntegral_apply]
    apply integral_congr_ae
    filter_upwards with s
    rw [one_mul,weight_apply,← action_apply]
    congr 1
    unfold source
    ring
  have hd (s : InteriorState) :
      BoundedExponentialTiltResponse.density interiorHaar (source a) (144*β) s=(root β a s)^2 := by
    rw [BoundedExponentialTiltResponse.density,hZ,root_sq]
    congr 1
    congr 1
    unfold source
    ring
  unfold law BoundedExponentialTiltResponse.tiltedMeasure
  simp_rw [hd]

/-- Strong common-Haar derivative at EVERY middle amplitude, with the clock kept fixed. -/
theorem amplitude_root_hasDerivAt (t x y z : ℝ) :
    HasDerivAt (fun r : ℝ => rootClass (1/t^2) ![t*x,t*r,t*z])
      (rootTangent (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)) y := by
  have h0 := rootClass_hasDerivAt (1/t^2) (![t*x,t*y,t*z]:Parameters) (t • FourCubeMixedMeanValue.basis 1)
  have h0' : HasDerivAt (fun h : ℝ => rootClass (1/t^2)
      ((![t*x,t*y,t*z]:Parameters)+h • (t • FourCubeMixedMeanValue.basis 1)))
      (rootTangent (1/t^2) ![t*x,t*y,t*z] (t • FourCubeMixedMeanValue.basis 1)) (y-y) := by
    simpa only [sub_self] using h0
  have h := HasDerivAt.comp_sub_const y y h0'
  convert h using 1
  funext r
  apply congrArg (rootClass (1/t^2))
  ext j
  fin_cases j <;> simp [FourCubeMixedMeanValue.basis,Pi.single_apply] <;> ring

private theorem interval_amplitude (x z y1 y2 r R : ℝ)
    (h1 : x^2+y1^2+z^2≤R) (h2 : x^2+y2^2+z^2≤R) (hr : r∈Icc y1 y2) :
    x^2+r^2+z^2≤R := by
  by_cases hp : 0≤r
  · have hs := pow_le_pow_left₀ hp hr.2 2
    linarith
  · have hn : 0≤-r := by linarith
    have hs := pow_le_pow_left₀ hn (neg_le_neg hr.1) 2
    simp only [neg_sq] at hs
    linarith

private theorem middle_segment_bound (t x z y1 y2 C : ℝ) (hC : 0<C) (hle : y1≤y2)
    (hb : ∀ r∈Icc y1 y2,
      ‖nativeResponse (1/t^2) ![t*x,t*r,t*z] (t • FourCubeMixedMeanValue.basis 1)‖^2≤C) :
    ‖rootClass (1/t^2) ![t*x,t*y2,t*z]-rootClass (1/t^2) ![t*x,t*y1,t*z]‖≤
      (Real.sqrt C/2)*(y2-y1) := by
  have hder (r : ℝ) (hr : r∈Ico y1 y2) :
      ‖rootTangent (1/t^2) ![t*x,t*r,t*z] (t • FourCubeMixedMeanValue.basis 1)‖≤Real.sqrt C/2 := by
    have hs := rootTangent_norm_square (1/t^2) (![t*x,t*r,t*z]:Parameters) (t • FourCubeMixedMeanValue.basis 1)
    rw [← nativeResponse_norm (1/t^2) ![t*x,t*r,t*z] (t • FourCubeMixedMeanValue.basis 1)] at hs
    nlinarith [hb r (Ico_subset_Icc_self hr),Real.sq_sqrt hC.le,Real.sqrt_nonneg C,
      norm_nonneg (rootTangent (1/t^2) ![t*x,t*r,t*z] (t • FourCubeMixedMeanValue.basis 1))]
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (a := y1) (b := y2)
    (f := fun r => rootClass (1/t^2) ![t*x,t*r,t*z])
    (f' := fun r => rootTangent (1/t^2) ![t*x,t*r,t*z] (t • FourCubeMixedMeanValue.basis 1))
    (fun r _ => (amplitude_root_hasDerivAt t x r z).hasDerivWithinAt) hder y2 (right_mem_Icc.mpr hle)

/-- Actual conditional laws are uniformly Lipschitz in square-root density distance
on each thermal amplitude ball. The constant is fixed-cell and need not be small. -/
theorem uniform_root_distance (R : ℝ) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x z y1 y2 : ℝ,
      x^2+y1^2+z^2≤R → x^2+y2^2+z^2≤R →
      ‖rootClass (1/t^2) ![t*x,t*y2,t*z]-rootClass (1/t^2) ![t*x,t*y1,t*z]‖≤K*|y2-y1| := by
  obtain ⟨C,hC,hbound⟩ := FourCubeThermalScore.uniform_middle_response R
  refine ⟨Real.sqrt C/2,div_pos (Real.sqrt_pos.mpr hC) (by norm_num),?_⟩
  filter_upwards [hbound] with t ht x z y1 y2 h1 h2
  by_cases hle : y1≤y2
  · have h := middle_segment_bound t x z y1 y2 C hC hle
      (fun r hr => ht x r z (interval_amplitude x z y1 y2 r R h1 h2 hr))
    simpa only [abs_of_nonneg (sub_nonneg.mpr hle)] using h
  · have hle' : y2≤y1 := le_of_not_ge hle
    have h := middle_segment_bound t x z y2 y1 C hC hle'
      (fun r hr => ht x r z (interval_amplitude x z y2 y1 r R h2 h1 hr))
    calc
      _ = ‖rootClass (1/t^2) ![t*x,t*y1,t*z]-rootClass (1/t^2) ![t*x,t*y2,t*z]‖ := norm_sub_rev _ _
      _ ≤ (Real.sqrt C/2)*(y1-y2) := h
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr hle'),neg_sub]

theorem rootClass_norm (β : ℝ) (a : Parameters) : ‖rootClass β a‖=1 := by
  nlinarith [rootClass_norm_square β a,norm_nonneg (rootClass β a)]

private def absObservable (f : Observables) : Observables := ⟨fun s => |f s|,f.continuous.abs⟩

private theorem abs_haar_norm (f : Observables) :
    ‖ContinuousMap.toLp 2 interiorHaar ℝ (absObservable f)‖=‖ContinuousMap.toLp 2 interiorHaar ℝ f‖ := by
  have he : ‖ContinuousMap.toLp 2 interiorHaar ℝ (absObservable f)‖^2=
      ‖ContinuousMap.toLp 2 interiorHaar ℝ f‖^2 := by
    rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,
      ContinuousMap.inner_toLp,ContinuousMap.inner_toLp]
    apply integral_congr_ae
    filter_upwards with s
    change |f s| * |f s|=f s*f s
    rw [← pow_two,sq_abs,pow_two]
  nlinarith [norm_nonneg (ContinuousMap.toLp 2 interiorHaar ℝ (absObservable f)),
    norm_nonneg (ContinuousMap.toLp 2 interiorHaar ℝ f)]

/-- Actual density L1 control, with no probability metric convention left implicit. -/
theorem density_l1_bound (β : ℝ) (a b : Parameters) :
    (∫ s,|(root β a s)^2-(root β b s)^2| ∂interiorHaar)≤2*‖rootClass β a-rootClass β b‖ := by
  let p := root β a-root β b
  let q := root β a+root β b
  have he : (∫ s,|(root β a s)^2-(root β b s)^2| ∂interiorHaar)=
      inner ℝ (ContinuousMap.toLp 2 interiorHaar ℝ (absObservable p))
        (ContinuousMap.toLp 2 interiorHaar ℝ q) := by
    rw [ContinuousMap.inner_toLp]
    apply integral_congr_ae
    filter_upwards with s
    change |(root β a s)^2-(root β b s)^2|=(root β a s+root β b s)*|root β a s-root β b s|
    rw [show (root β a s)^2-(root β b s)^2=(root β a s-root β b s)*(root β a s+root β b s) by ring,
      abs_mul,abs_of_pos (add_pos (root_pos β a s) (root_pos β b s)),mul_comm]
  have hp : ‖ContinuousMap.toLp 2 interiorHaar ℝ (absObservable p)‖=‖rootClass β a-rootClass β b‖ := by
    rw [abs_haar_norm]
    change ‖ContinuousMap.toLp 2 interiorHaar ℝ (root β a-root β b)‖=_
    rw [map_sub]
    rfl
  have hq : ‖ContinuousMap.toLp 2 interiorHaar ℝ q‖≤2 := by
    change ‖ContinuousMap.toLp 2 interiorHaar ℝ (root β a+root β b)‖≤2
    rw [map_add]
    exact (norm_add_le _ _).trans (by rw [show ContinuousMap.toLp 2 interiorHaar ℝ (root β a)=rootClass β a by rfl,
      show ContinuousMap.toLp 2 interiorHaar ℝ (root β b)=rootClass β b by rfl,rootClass_norm,rootClass_norm]; norm_num)
  rw [he]
  apply (real_inner_le_norm _ _).trans
  rw [hp]
  exact (mul_le_mul_of_nonneg_left hq (norm_nonneg _)).trans_eq (mul_comm _ _)

theorem law_integral_root (β : ℝ) (a : Parameters) (f : InteriorState → ℝ) :
    (∫ s,f s ∂law β a)=∫ s,f s*(root β a s)^2 ∂interiorHaar := by
  have hm : Measurable (fun s => (root β a s)^2) := (root β a).continuous.measurable.pow_const 2
  rw [law_root_density,integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul,mul_comm]

private theorem bounded_mul_integrable (f : InteriorState → ℝ) (hf : Measurable f)
    (M : ℝ) (hM : 0≤M) (hb : ∀ s,|f s|≤M) (w : Observables) :
    Integrable (fun s => f s*w s) interiorHaar := by
  apply Integrable.of_bound (hf.mul w.continuous.measurable).aestronglyMeasurable (M*‖w‖)
  filter_upwards with s
  change ‖f s*w s‖≤M*‖w‖
  rw [Real.norm_eq_abs,abs_mul]
  exact mul_le_mul (hb s) (by simpa only [Real.norm_eq_abs] using w.norm_coe_le_norm s)
    (abs_nonneg _) hM

/-- Bounded measurable tests compare the ACTUAL conditional measures, not just continuous cores. -/
theorem bounded_test_difference (β : ℝ) (a b : Parameters) (f : InteriorState → ℝ)
    (hf : Measurable f) (M : ℝ) (hM : 0≤M) (hb : ∀ s,|f s|≤M) :
    |(∫ s,f s ∂law β a)-(∫ s,f s ∂law β b)|≤2*M*‖rootClass β a-rootClass β b‖ := by
  have ha : Integrable (fun s => f s*(root β a s)^2) interiorHaar := by
    simpa only [ContinuousMap.mul_apply,pow_two] using bounded_mul_integrable f hf M hM hb (root β a*root β a)
  have hb' : Integrable (fun s => f s*(root β b s)^2) interiorHaar := by
    simpa only [ContinuousMap.mul_apply,pow_two] using bounded_mul_integrable f hf M hM hb (root β b*root β b)
  have hright : Integrable (fun s => M*|(root β a s)^2-(root β b s)^2|) interiorHaar := by
    have h := (observable_integrable (absObservable (root β a*root β a-root β b*root β b))).const_mul M
    convert h using 1
    funext s
    change M*|(root β a s)^2-(root β b s)^2|=
      M*|root β a s*root β a s-root β b s*root β b s|
    simp only [pow_two]
  rw [law_integral_root,law_integral_root,← integral_sub ha hb']
  calc
    _ ≤ ∫ s,|f s*(root β a s)^2-f s*(root β b s)^2| ∂interiorHaar :=
      by simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := interiorHaar)
          (fun s => f s*(root β a s)^2-f s*(root β b s)^2))
    _ ≤ ∫ s,M*|(root β a s)^2-(root β b s)^2| ∂interiorHaar := by
      apply integral_mono (ha.sub hb').norm hright
      intro s
      change ‖f s*(root β a s)^2-f s*(root β b s)^2‖≤M*|(root β a s)^2-(root β b s)^2|
      rw [Real.norm_eq_abs,← mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_right (hb s) (abs_nonneg _)
    _ = M*(∫ s,|(root β a s)^2-(root β b s)^2| ∂interiorHaar) := integral_const_mul _ _
    _ ≤ M*(2*‖rootClass β a-rootClass β b‖) :=
      mul_le_mul_of_nonneg_left (density_l1_bound β a b) hM
    _ = _ := by ring

/-- Common thermal Lipschitz control for ALL bounded measurable conditional tests. -/
theorem uniform_bounded_tests (R : ℝ) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ t : ℝ in 𝓝[≠] 0,∀ x z y1 y2 : ℝ,
      x^2+y1^2+z^2≤R → x^2+y2^2+z^2≤R →
      ∀ f : InteriorState → ℝ,Measurable f → (∀ s,|f s|≤1) →
      |(∫ s,f s ∂law (1/t^2) ![t*x,t*y2,t*z])-(∫ s,f s ∂law (1/t^2) ![t*x,t*y1,t*z])|≤K*|y2-y1| := by
  obtain ⟨K,hK,hbound⟩ := uniform_root_distance R
  refine ⟨2*K,by positivity,?_⟩
  filter_upwards [hbound] with t ht x z y1 y2 h1 h2 f hf hb
  have h := bounded_test_difference (1/t^2) (![t*x,t*y2,t*z]:Parameters)
    (![t*x,t*y1,t*z]:Parameters) f hf 1 (by norm_num) hb
  have hroot := mul_le_mul_of_nonneg_left (ht x z y1 y2 h1 h2) (by norm_num : (0:ℝ)≤2)
  simp only [mul_one] at h
  simpa only [mul_assoc] using h.trans hroot
end OperatorDerivativeRewrite.Foundation.FourCubeHaarHalfDensity
