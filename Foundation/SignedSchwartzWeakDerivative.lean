import Foundation.SignedSchwartzL2Rigging

/-! Actual distributional identities identifying a closed weighted derivative relation. -/
noncomputable section
open MeasureTheory Filter
open scoped SchwartzMap Topology
namespace OperatorDerivativeRewrite.Foundation.SignedSchwartzWeakDerivative
open SignedSchwartzL2Rigging
set_option backward.isDefEq.respectTransparency false

theorem distributionEmbedding_apply (K : 𝓢(ℝ,ℝ)) (u : H K) (g : 𝓢(ℝ,ℂ)) :
    distributionEmbedding K u g = ∫ x : ℝ, g x*u x ∂measure K := by
  change Lp.toTemperedDistributionCLM ℂ (measure K) 2 u g = _
  rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_apply]
  rfl

theorem embed_apply (K : 𝓢(ℝ,ℝ)) (u : H K) (g : 𝓢(ℝ,ℂ)) :
    embed K u g = ∫ x : ℝ, g x*((|K x|:ℝ):ℂ)*u x ∂measure K := by
  rw [embed, ContinuousLinearMap.comp_apply, distributionEmbedding_apply]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_coeFn (H := ℂ) (fun x => |K x|) (abs_memLp_top K) u] with x hx
  try dsimp only
  rw [hx, Complex.real_smul]
  ring

theorem driftEmbedding_apply (K : 𝓢(ℝ,ℝ)) (u : H K) (g : 𝓢(ℝ,ℂ)) :
    driftEmbedding K u g = ∫ x : ℝ, g x*(drift K x:ℂ)*u x ∂measure K := by
  rw [driftEmbedding, ContinuousLinearMap.comp_apply, distributionEmbedding_apply]
  apply integral_congr_ae
  filter_upwards [boundedMultiplier_coeFn (H := ℂ) (drift K) (drift_memLp_top K) u] with x hx
  try dsimp only
  rw [hx, Complex.real_smul]
  ring

theorem embed_schwartz (K : 𝓢(ℝ,ℝ)) (f g : 𝓢(ℝ,ℂ)) :
    embed K (f.toLp 2 (measure K)) g = ∫ x : ℝ, g x*f x*(K x:ℂ)^2 := by
  have he : embed K (f.toLp 2 (measure K)) g =
      ∫ x : ℝ, g x*((|K x|:ℝ):ℂ)*f x ∂measure K := by
    rw [embed_apply]
    apply integral_congr_ae
    filter_upwards [f.coeFn_toLp 2 (measure K)] with x hx
    try dsimp only
    rw [hx]
  have hm : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  rw [he, SignedSchwartzL2Rigging.measure, SignedAbsoluteIntegration.absoluteDensity,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    try dsimp only
    rw [ENNReal.toReal_ofReal (abs_nonneg _), Complex.real_smul]
    have hs : ((|K x|:ℝ):ℂ)^2=(K x:ℂ)^2 := by exact_mod_cast sq_abs (K x)
    calc
      _ = g x*f x*((|K x|:ℝ):ℂ)^2 := by ring
      _ = _ := by rw [hs]

theorem driftEmbedding_schwartz (K : 𝓢(ℝ,ℝ)) (f g : 𝓢(ℝ,ℂ)) :
    driftEmbedding K (f.toLp 2 (measure K)) g =
      ∫ x : ℝ, g x*f x*(2*(K x:ℂ)*((deriv K x:ℝ):ℂ)) := by
  have he : driftEmbedding K (f.toLp 2 (measure K)) g =
      ∫ x : ℝ, g x*(drift K x:ℂ)*f x ∂measure K := by
    rw [driftEmbedding_apply]
    apply integral_congr_ae
    filter_upwards [f.coeFn_toLp 2 (measure K)] with x hx
    try dsimp only
    rw [hx]
  have hm : Measurable (fun x : ℝ => |K x|) := by
    simpa only [Real.norm_eq_abs] using K.continuous.measurable.norm
  rw [he, SignedSchwartzL2Rigging.measure, SignedAbsoluteIntegration.absoluteDensity,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    try dsimp only
    rw [ENNReal.toReal_ofReal (abs_nonneg _), Complex.real_smul]
    calc
      _ = g x*f x*(((|K x|:ℝ):ℂ)*(drift K x:ℂ)) := by ring
      _ = _ := by rw [← Complex.ofReal_mul, drift_density]; push_cast; ring

def testWeight (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) : 𝓢(ℝ,ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun x : ℝ => (K x)^2) g

theorem testWeight_apply (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    testWeight K g x = (K x:ℂ)^2*g x := by
  have hg : (fun x : ℝ => (K x)^2).HasTemperateGrowth := K.hasTemperateGrowth.pow 2
  rw [testWeight, SchwartzMap.smulLeftCLM_apply hg]
  change (K x)^2 • g x = _
  rw [Complex.real_smul]
  push_cast
  rfl

theorem testWeight_deriv (K : 𝓢(ℝ,ℝ)) (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    deriv (testWeight K g) x =
      2*(K x:ℂ)*((deriv K x:ℝ):ℂ)*g x+(K x:ℂ)^2*deriv g x := by
  have he : (testWeight K g : ℝ → ℂ) = (fun y : ℝ => (K y:ℂ)^2*g y) :=
    funext (testWeight_apply K g)
  rw [he]
  have hk : HasDerivAt (fun y : ℝ => (K y:ℂ)) ((deriv K x:ℝ):ℂ) x :=
    (K.hasDerivAt x).ofReal_comp
  have hh : HasDerivAt (fun y : ℝ => (K y:ℂ)^2*g y)
      (2*(K x:ℂ)*((deriv K x:ℝ):ℂ)*g x+(K x:ℂ)^2*deriv g x) x := by
    convert (hk.pow 2).mul (g.hasDerivAt x) using 1 <;> norm_num <;> ring
  exact hh.deriv

theorem core_identity (K : 𝓢(ℝ,ℝ)) (f : 𝓢(ℝ,ℂ)) :
    embed K ((SchwartzMap.derivCLM ℂ ℂ f).toLp 2 (measure K)) =
      TemperedDistribution.derivCLM ℂ (embed K (f.toLp 2 (measure K))) -
        driftEmbedding K (f.toLp 2 (measure K)) := by
  ext g
  change embed K ((SchwartzMap.derivCLM ℂ ℂ f).toLp 2 (measure K)) g =
    embed K (f.toLp 2 (measure K)) (-SchwartzMap.derivCLM ℂ ℂ g) -
      driftEmbedding K (f.toLp 2 (measure K)) g
  rw [map_neg]
  have h := SchwartzMap.integral_mul_deriv_eq_neg_deriv_mul f (testWeight K g)
  have hiB : Integrable (fun x : ℝ => f x*((K x:ℂ)^2*deriv g x)) := by
    convert (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
      (testWeight K (SchwartzMap.derivCLM ℂ ℂ g))).integrable (μ := volume) using 1
    funext x
    simp only [SchwartzMap.pairing_apply, ContinuousLinearMap.mul_apply', testWeight_apply,
      SchwartzMap.derivCLM_apply]
  have hiT : Integrable (fun x : ℝ => f x*deriv (testWeight K g) x) := by
    convert (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) f
      (SchwartzMap.derivCLM ℂ ℂ (testWeight K g))).integrable (μ := volume) using 1
    funext x
    simp only [SchwartzMap.pairing_apply, ContinuousLinearMap.mul_apply', SchwartzMap.derivCLM_apply]
  have hiA : Integrable (fun x : ℝ => f x*(2*(K x:ℂ)*((deriv K x:ℝ):ℂ)*g x)) := by
    apply (hiT.sub hiB).congr
    exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply]
      try dsimp only
      rw [testWeight_deriv]
      ring
  have he : (∫ x : ℝ, f x*deriv (testWeight K g) x) =
      (∫ x : ℝ, f x*(2*(K x:ℂ)*((deriv K x:ℝ):ℂ)*g x)) +
      (∫ x : ℝ, f x*((K x:ℂ)^2*deriv g x)) := by
    rw [← integral_add hiA hiB]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; rw [testWeight_deriv]; ring
  rw [he] at h
  rw [embed_schwartz, embed_schwartz, driftEmbedding_schwartz]
  simp only [SchwartzMap.derivCLM_apply]
  simp_rw [testWeight_apply] at h
  have haE : (∫ x : ℝ, g x*f x*(2*(K x:ℂ)*((deriv K x:ℝ):ℂ))) =
      (∫ x : ℝ, f x*(2*(K x:ℂ)*((deriv K x:ℝ):ℂ)*g x)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; ring
  have hbE : (∫ x : ℝ, deriv g x*f x*(K x:ℂ)^2) =
      (∫ x : ℝ, f x*((K x:ℂ)^2*deriv g x)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; ring
  have hdE : (∫ x : ℝ, g x*deriv f x*(K x:ℂ)^2) =
      (∫ x : ℝ, deriv f x*((K x:ℂ)^2*g x)) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; ring
  rw [haE, hbE, hdE]
  linear_combination h

end OperatorDerivativeRewrite.Foundation.SignedSchwartzWeakDerivative
