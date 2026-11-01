import Foundation.PeriodicConditionalEndpointScore
import Foundation.PeriodicPhysicalBridgeScore
import Foundation.HilbertRepresentation

/-! Native middle/rest compression for the original boundary-conditioned Wilson law.
The two pullbacks are genuine isometries because their actual marginals agree.
No product independence, Gaussian transport, or physical transfer gap is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory

namespace OperatorDerivativeRewrite.Foundation.PeriodicNativeCompression
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab
open HilbertRepresentation
attribute [local irreducible] PeriodicGroundBridge.law PeriodicAugmentedBridge.law
  PeriodicLinkDisintegration.marginal PeriodicLinkDisintegration.split

abbrev Middle (β : ℝ) (U W : State) := Lp ℝ 2 (PeriodicGroundBridge.law β U W)
abbrev Joint (β : ℝ) (U W : State) := Lp ℝ 2 (PeriodicAugmentedBridge.law β U W)
abbrev Rest (e : SpatialEdge) (β : ℝ) (U W : State) :=
  Lp ℝ 2 (PeriodicLinkDisintegration.marginal e β U W)

/-- Exact pullback from the physical middle law, not the reference Haar law. -/
def middleLift (β : ℝ) (U W : State) : Middle β U W →ₗᵢ[ℝ] Joint β U W :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst (PeriodicAugmentedBridge.projection_preserving β U W)

/-- Exact rest pullback retains both temporal fields and the spatial partition. -/
def restLift (e : SpatialEdge) (β : ℝ) (U W : State) : Rest e β U W →ₗᵢ[ℝ] Joint β U W :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun q => ((PeriodicLinkDisintegration.split e) q).1)
    (PeriodicConditionalEndpointScore.rest_preserving e β U W)

/-- Actual conditional averaging, defined on the entire native L2 domain. -/
def channel (e : SpatialEdge) (β : ℝ) (U W : State) :
    Middle β U W →L[ℝ] Rest e β U W :=
  (predictableAdjoint (restLift e β U W)).comp (middleLift β U W).toContinuousLinearMap

/-- The collapsed physical-middle operator is a Gram compression. -/
def compression (e : SpatialEdge) (β : ℝ) (U W : State) :
    Middle β U W →L[ℝ] Middle β U W :=
  (channel e β U W).adjoint.comp (channel e β U W)

/-- Innovation in the ORIGINAL augmented norm. -/
def residual (e : SpatialEdge) (β : ℝ) (U W : State) :
    Middle β U W →L[ℝ] Joint β U W :=
  (middleLift β U W).toContinuousLinearMap -
    (restLift e β U W).toContinuousLinearMap.comp (channel e β U W)

theorem channel_pairing (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) (g : Rest e β U W) :
    inner ℝ (channel e β U W f) g =
      inner ℝ (middleLift β U W f) (restLift e β U W g) := by
  change inner ℝ (predictableAdjoint (restLift e β U W) (middleLift β U W f)) g = _
  exact predictableAdjoint_pairing (restLift e β U W) (middleLift β U W f) g

theorem residual_orthogonal (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) (g : Rest e β U W) :
    inner ℝ (residual e β U W f) (restLift e β U W g) = 0 :=
  representation_residual_pairing (restLift e β U W) (middleLift β U W f) g

/-- Full-domain native Pythagoras; no predictable representation assumption. -/
theorem norm_decomposition (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    ‖f‖^2 = ‖channel e β U W f‖^2 + ‖residual e β U W f‖^2 := by
  have h := representation_norm_decomposition (restLift e β U W) (middleLift β U W f)
  rw [(middleLift β U W).norm_map] at h
  exact h

theorem compression_pairing (e : SpatialEdge) (β : ℝ) (U W : State)
    (f g : Middle β U W) :
    inner ℝ (compression e β U W f) g =
      inner ℝ (channel e β U W f) (channel e β U W g) :=
  (channel e β U W).adjoint_inner_left _ _

/-- The Dirichlet form is exactly the native conditional innovation Gram. -/
theorem residual_gram (e : SpatialEdge) (β : ℝ) (U W : State)
    (f g : Middle β U W) :
    inner ℝ (f-compression e β U W f) g =
      inner ℝ (residual e β U W f) (residual e β U W g) := by
  have h1 := residual_orthogonal e β U W f (channel e β U W g)
  have h2 := channel_pairing e β U W g (channel e β U W f)
  rw [real_inner_comm] at h2
  have h3 : inner ℝ (restLift e β U W (channel e β U W f)) (middleLift β U W g) =
      inner ℝ (channel e β U W f) (channel e β U W g) := by
    rw [real_inner_comm]
    exact h2.symm
  change inner ℝ (middleLift β U W f-restLift e β U W (channel e β U W f))
    (restLift e β U W (channel e β U W g)) = 0 at h1
  change inner ℝ (f-compression e β U W f) g =
    inner ℝ (middleLift β U W f-restLift e β U W (channel e β U W f))
      (middleLift β U W g-restLift e β U W (channel e β U W g))
  simp only [inner_sub_left, inner_sub_right, (middleLift β U W).inner_map_map,
    (restLift e β U W).inner_map_map, real_inner_comm (restLift e β U W
      (channel e β U W f)) (middleLift β U W g)] at h1 ⊢
  rw [compression_pairing]
  linarith

theorem dirichlet_identity (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    inner ℝ (f-compression e β U W f) f = ‖residual e β U W f‖^2 := by
  rw [residual_gram, real_inner_self_eq_norm_sq]

theorem compression_positive (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) : 0 ≤ inner ℝ (compression e β U W f) f := by
  rw [compression_pairing, real_inner_self_eq_norm_sq]
  exact sq_nonneg _

theorem compression_symmetric (e : SpatialEdge) (β : ℝ) (U W : State)
    (f g : Middle β U W) :
    inner ℝ (compression e β U W f) g = inner ℝ f (compression e β U W g) := by
  calc
    _ = inner ℝ (channel e β U W f) (channel e β U W g) := compression_pairing e β U W f g
    _ = inner ℝ (channel e β U W g) (channel e β U W f) := real_inner_comm _ _
    _ = inner ℝ (compression e β U W g) f := (compression_pairing e β U W g f).symm
    _ = _ := real_inner_comm _ _

/-- Zero innovation is precisely actual rest-representability of the lifted observable. -/
theorem residual_zero_iff (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    residual e β U W f = 0 ↔
      middleLift β U W f ∈ (restLift e β U W).toLinearMap.range := by
  change middleLift β U W f - representationProjection (restLift e β U W)
    (middleLift β U W f) = 0 ↔ _
  rw [sub_eq_zero, eq_comm]
  exact representationProjection_eq_self_iff _ _

theorem compression_fixed_iff (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    compression e β U W f = f ↔ residual e β U W f = 0 := by
  constructor
  · intro h
    have hd := dirichlet_identity e β U W f
    rw [h, sub_self, inner_zero_left] at hd
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (residual e β U W f)])
  · intro h
    apply ext_inner_right ℝ
    intro g
    have hd := residual_gram e β U W f g
    rw [h, inner_zero_left, inner_sub_left] at hd
    linarith

/-- A native multiblock lower frame is EXACTLY a Dirichlet coercivity statement.
Neither side is asserted to hold uniformly in beta, volume, or physical scale. -/
theorem multiblock_frame_iff (β : ℝ) (U W : State)
    (s : Finset SpatialEdge) (κ : ℝ) (f : Middle β U W) :
    κ*‖f‖^2 ≤ ∑ e ∈ s, ‖residual e β U W f‖^2 ↔
      κ*‖f‖^2 ≤ ∑ e ∈ s, inner ℝ (f-compression e β U W f) f := by
  simp_rw [dirichlet_identity]

/-- Literal saved Wilson conditional integral, with its true exterior marginal. -/
def conditionalMean (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : PeriodicAugmentedBridge.Space → ℝ) (r : PeriodicLinkDisintegration.Rest e) : ℝ :=
  ∫ A, f ((PeriodicLinkDisintegration.split e).symm (r,A))
    ∂PeriodicLinkDisintegration.conditionalKernel e β U W r

theorem conditionalMean_measurable (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : PeriodicAugmentedBridge.Space → ℝ) (hf : Measurable f) :
    Measurable (conditionalMean e β U W f) := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  exact (hf.comp (PeriodicLinkDisintegration.split e).symm.measurable).stronglyMeasurable.integral_kernel_prod_right'.measurable

theorem conditionalMean_bound (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : PeriodicAugmentedBridge.Space → ℝ) (M : ℝ) (hb : ∀ q, |f q| ≤ M)
    (r : PeriodicLinkDisintegration.Rest e) : |conditionalMean e β U W f r| ≤ M := by
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  simpa only [conditionalMean, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := PeriodicLinkDisintegration.conditionalKernel e β U W r)
      (f := fun A => f ((PeriodicLinkDisintegration.split e).symm (r,A)))
      (C := M)
      (ae_of_all _ (fun A => by simpa only [Real.norm_eq_abs] using hb _))

theorem conditionalMean_memLp (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : PeriodicAugmentedBridge.Space → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ q, |f q| ≤ M) :
    MemLp (conditionalMean e β U W f) 2 (PeriodicLinkDisintegration.marginal e β U W) := by
  letI := PeriodicLinkDisintegration.marginal_probability e β U W
  apply MemLp.of_bound (conditionalMean_measurable e β U W f hf).aestronglyMeasurable M
  filter_upwards with r
  simpa only [Real.norm_eq_abs] using (conditionalMean_bound e β U W f M hb r)

/-- Identification against EVERY native rest-L2 test, not an assumed row formula. -/
theorem rest_adjoint_kernel (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : PeriodicAugmentedBridge.Space → ℝ) (hf : Measurable f)
    (M : ℝ) (hb : ∀ q, |f q| ≤ M)
    (hm : MemLp f 2 (PeriodicAugmentedBridge.law β U W)) :
    predictableAdjoint (restLift e β U W) (hm.toLp f) =
      (conditionalMean_memLp e β U W f hf M hb).toLp (conditionalMean e β U W f) := by
  letI := PeriodicLinkDisintegration.marginal_probability e β U W
  letI := PeriodicLinkDisintegration.kernel_markov e β U W
  let μ := PeriodicLinkDisintegration.marginal e β U W
  let K := PeriodicLinkDisintegration.conditionalKernel e β U W
  have hp : MeasurePreserving Prod.fst (μ ⊗ₘ K) μ :=
    ⟨measurable_fst, Measure.fst_compProd μ K⟩
  have hs : MeasurePreserving (PeriodicLinkDisintegration.split e)
      (PeriodicAugmentedBridge.law β U W) (μ ⊗ₘ K) :=
    ⟨(PeriodicLinkDisintegration.split e).measurable,
      PeriodicLinkDisintegration.actual_factorization e β U W⟩
  apply ext_inner_right ℝ
  intro g
  rw [predictableAdjoint_pairing, L2.inner_def, L2.inner_def]
  have he1 := Lp.coeFn_compMeasurePreserving g
    (PeriodicConditionalEndpointScore.rest_preserving e β U W)
  have he2 := (conditionalMean_memLp e β U W f hf M hb).coeFn_toLp
  have hi : Integrable (fun z : PeriodicLinkDisintegration.Rest e × SU2 =>
      f ((PeriodicLinkDisintegration.split e).symm z)*g z.1) (μ ⊗ₘ K) :=
    (hp.integrable_comp_of_integrable ((Lp.memLp g).integrable (by norm_num))).bdd_mul
      (hf.comp (PeriodicLinkDisintegration.split e).symm.measurable).aestronglyMeasurable
      (ae_of_all _ (fun z => by simpa only [Real.norm_eq_abs] using hb _))
  calc
    _ = ∫ q, f q*g (((PeriodicLinkDisintegration.split e) q).1)
        ∂PeriodicAugmentedBridge.law β U W := by
      apply integral_congr_ae
      filter_upwards [hm.coeFn_toLp, he1] with q hq hg
      change inner ℝ ((hm.toLp f) q) ((Lp.compMeasurePreserving _ _ g) q) = _
      rw [hq, hg]
      simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial,
        Function.comp_def, mul_comm]
    _ = ∫ z, f ((PeriodicLinkDisintegration.split e).symm z)*g z.1 ∂(μ ⊗ₘ K) := by
      rw [← hs.integral_comp' (fun z => f ((PeriodicLinkDisintegration.split e).symm z)*g z.1)]
      simp only [(PeriodicLinkDisintegration.split e).symm_apply_apply]
    _ = ∫ r, conditionalMean e β U W f r*g r ∂μ := by
      rw [Measure.integral_compProd hi]
      simp only [conditionalMean, integral_mul_const, μ, K]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [he2] with r hr
      rw [hr]
      simp only [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, mul_comm]

/-- Actual bounded physical observables use the true signed-free Wilson row. -/
theorem channel_kernel (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : State → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ V, |f V| ≤ M)
    (hm : MemLp f 2 (PeriodicGroundBridge.law β U W)) :
    channel e β U W (hm.toLp f) =
      (conditionalMean_memLp e β U W (fun q => f q.1) (hf.comp measurable_fst)
        M (fun q => hb q.1)).toLp (conditionalMean e β U W (fun q => f q.1)) := by
  exact rest_adjoint_kernel e β U W (fun q => f q.1) (hf.comp measurable_fst)
    M (fun q => hb q.1) (hm.comp_measurePreserving (PeriodicAugmentedBridge.projection_preserving β U W))

theorem channel_contraction (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) : ‖channel e β U W f‖ ≤ ‖f‖ := by
  have h := norm_decomposition e β U W f
  nlinarith [norm_nonneg f, norm_nonneg (channel e β U W f),
    sq_nonneg ‖residual e β U W f‖]

theorem compression_norm_le_one (e : SpatialEdge) (β : ℝ) (U W : State) :
    ‖compression e β U W‖ ≤ 1 := by
  have h : ‖channel e β U W‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    simpa only [one_mul] using channel_contraction e β U W f
  calc
    _ ≤ ‖(channel e β U W).adjoint‖*‖channel e β U W‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖channel e β U W‖*‖channel e β U W‖ := by rw [ContinuousLinearMap.adjoint.norm_map]
    _ ≤ 1 := by nlinarith [norm_nonneg (channel e β U W)]

/-- Literal C* Q C, with Q the actual closed rest-range projection. -/
theorem compression_as_projection (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : Middle β U W) :
    compression e β U W f = predictableAdjoint (middleLift β U W)
      (representationProjection (restLift e β U W) (middleLift β U W f)) := by
  apply ext_inner_right ℝ
  intro g
  rw [compression_pairing, predictableAdjoint_pairing]
  change inner ℝ (channel e β U W f) (channel e β U W g) =
    inner ℝ (restLift e β U W (channel e β U W f)) (middleLift β U W g)
  calc
    _ = inner ℝ (channel e β U W g) (channel e β U W f) := real_inner_comm _ _
    _ = inner ℝ (middleLift β U W g) (restLift e β U W (channel e β U W f)) :=
      channel_pairing e β U W g (channel e β U W f)
    _ = _ := real_inner_comm _ _

theorem residual_kernel_ae (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : State → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ V, |f V| ≤ M)
    (hm : MemLp f 2 (PeriodicGroundBridge.law β U W)) :
    residual e β U W (hm.toLp f) =ᵐ[PeriodicAugmentedBridge.law β U W]
      fun q => f q.1-conditionalMean e β U W (fun z => f z.1)
        (((PeriodicLinkDisintegration.split e) q).1) := by
  change (middleLift β U W (hm.toLp f)-restLift e β U W (channel e β U W (hm.toLp f))) =ᵐ[_] _
  rw [channel_kernel e β U W f hf M hb hm]
  let hn := conditionalMean_memLp e β U W (fun q => f q.1) (hf.comp measurable_fst) M (fun q => hb q.1)
  have h1 := (hm.comp_measurePreserving (PeriodicAugmentedBridge.projection_preserving β U W)).coeFn_toLp
  have h2 := (hn.comp_measurePreserving (PeriodicConditionalEndpointScore.rest_preserving e β U W)).coeFn_toLp
  filter_upwards [Lp.coeFn_sub (middleLift β U W (hm.toLp f))
    (restLift e β U W (hn.toLp _)), h1, h2] with q hq hm hn
  exact hq.trans (congrArg₂ (fun x y : ℝ => x-y) hm hn)

/-- The original Wilson conditional variance is the native compressed Dirichlet
form. No independent-link model, stationary-endpoint averaging, or new norm. -/
theorem dirichlet_kernel (e : SpatialEdge) (β : ℝ) (U W : State)
    (f : State → ℝ) (hf : Measurable f) (M : ℝ) (hb : ∀ V, |f V| ≤ M)
    (hm : MemLp f 2 (PeriodicGroundBridge.law β U W)) :
    inner ℝ (hm.toLp f-compression e β U W (hm.toLp f)) (hm.toLp f) =
      ∫ q, (f q.1-conditionalMean e β U W (fun z => f z.1)
        (((PeriodicLinkDisintegration.split e) q).1))^2 ∂PeriodicAugmentedBridge.law β U W := by
  rw [dirichlet_identity, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [residual_kernel_ae e β U W f hf M hb hm] with q hq
  rw [hq]
  simp only [RCLike.inner_apply, conj_trivial, pow_two]

end OperatorDerivativeRewrite.Foundation.PeriodicNativeCompression
