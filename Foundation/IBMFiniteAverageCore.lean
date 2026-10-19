import Foundation.IBMNonlinearAverageGraph

/-! Finite families of actual IBM averages and bounded nonlinear tests in the
intersection of the two partial derivative domains and intrinsic observable L2. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMFiniteAverageCore
open InfiniteGaussian IBMTimeAveragedObservable IBMNonlinearAverageGraph
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] nativeAverage sourceAverage IBMConstructedSources.clockPath

abbrev partialDerivative := BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative

def clockDomain : Submodule ℝ JointL2 := partialDerivative.domain.comap
  (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).toLinearEquiv.toLinearMap

def sourceDomain : Submodule ℝ JointL2 := partialDerivative.domain.comap
  ((ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).toLinearEquiv.toLinearMap.comp
    (ProductL2Curry.swap gaussianProduct gaussianProduct).toLinearMap)

/-- Actual intrinsic IBM observables with both existing partial derivatives. -/
def intrinsicCore : Submodule ℝ JointL2 := IntrinsicSpace ⊓ clockDomain ⊓ sourceDomain

theorem mem_intrinsicCore_iff (f : JointL2) : f ∈ intrinsicCore ↔
    f ∈ IntrinsicSpace ∧
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct f ∈ partialDerivative.domain ∧
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct f) ∈ partialDerivative.domain := by
  change ((f ∈ IntrinsicSpace ∧
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct f ∈ partialDerivative.domain) ∧
    ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct f) ∈ partialDerivative.domain) ↔ _
  exact and_assoc

theorem nativeAverage_mem (T : ℝ) (hT : 0 ≤ T) : nativeAverage T ∈ intrinsicCore := by
  apply (mem_intrinsicCore_iff _).mpr
  obtain ⟨hc, _⟩ := IBMClockAverageGraph.nativeAverage_clock_domain hT
  refine ⟨nativeAverage_intrinsic T, hc, ?_⟩
  rw [nativeAverage_source_representation]
  exact LinearPMap.mem_domain_of_mem_graph (sourceAverage_source_graph T)

/-- Bounded analytic composition preserves the actual common intrinsic domain,
not just the class of individual averages. -/
theorem bounded_chain (f : JointL2) (hf : f ∈ intrinsicCore)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : JointL2, F ∈ intrinsicCore ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (f ω) := by
  obtain ⟨hobs, hclock, hsource⟩ := (mem_intrinsicCore_iff _).mp hf
  let gc := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
    (partialDerivative ⟨_, hclock⟩)
  have hcg : (ProductL2Curry.curry gaussianProduct gaussianProduct f,
      ProductL2Curry.curry gaussianProduct gaussianProduct gc) ∈ partialDerivative.graph := by
    change (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct f,
      ProductL2Curry.curryEquiv gaussianProduct gaussianProduct gc) ∈ _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact partialDerivative.mem_graph ⟨_, hclock⟩
  obtain ⟨F, Gc, hFc, hF, _⟩ := GaussianClosedChainRule.bounded_product_chain_graph
    f gc hcg φ dφ hd hc A B hA hB
  let gs := (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct).symm
    (partialDerivative ⟨_, hsource⟩)
  have hsg : (ProductL2Curry.curry gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct f),
      ProductL2Curry.curry gaussianProduct gaussianProduct gs) ∈ partialDerivative.graph := by
    change (ProductL2Curry.curryEquiv gaussianProduct gaussianProduct
      (ProductL2Curry.swap gaussianProduct gaussianProduct f),
      ProductL2Curry.curryEquiv gaussianProduct gaussianProduct gs) ∈ _
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact partialDerivative.mem_graph ⟨_, hsource⟩
  obtain ⟨Fs, Gs, hFs, hFsae, _⟩ := GaussianClosedChainRule.bounded_product_chain_graph
    (ProductL2Curry.swap gaussianProduct gaussianProduct f) gs hsg φ dφ hd hc A B hA hB
  have he : ProductL2Curry.swap gaussianProduct gaussianProduct F = Fs := by
    apply Lp.ext
    have hs := measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hF
    filter_upwards [ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct F,
      ProductL2Curry.swap_coeFn gaussianProduct gaussianProduct f, hs, hFsae]
      with ω h1 h2 h3 h4
    rw [h1, h4, h2]
    exact h3
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  refine ⟨F, (mem_intrinsicCore_iff _).mpr ⟨?_, ?_, ?_⟩, hF⟩
  · exact mem_lpMeas_iff_aestronglyMeasurable.mpr
      ((hφ.comp_aestronglyMeasurable
        (mem_lpMeas_iff_aestronglyMeasurable.mp hobs)).congr hF.symm)
  · exact LinearPMap.mem_domain_of_mem_graph hFc
  · rw [he]
    exact LinearPMap.mem_domain_of_mem_graph hFs

def averageCombination {I : Type*} [Fintype I] (w t : I → ℝ) : JointL2 :=
  ∑ i, w i • nativeAverage (t i)

theorem averageCombination_mem {I : Type*} [Fintype I] (w t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) : averageCombination w t ∈ intrinsicCore := by
  classical
  exact intrinsicCore.sum_mem (fun i _ => intrinsicCore.smul_mem (w i) (nativeAverage_mem (t i) (ht i)))

theorem averageCombination_ae {I : Type*} [Fintype I] (w t : I → ℝ) :
    averageCombination w t =ᵐ[IBMSourceLaws.jointMeasure]
      fun ω => ∑ i, w i * nativeAverage (t i) ω := by
  classical
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i => w i • nativeAverage (t i)),
    ae_all_iff.mpr (fun i => Lp.coeFn_smul (w i) (nativeAverage (t i)))] with ω hs hm
  change (∑ i, w i • nativeAverage (t i)) ω = _
  rw [hs]
  simp only [Finset.sum_apply, hm, Pi.smul_apply, smul_eq_mul]

/-- Smooth bounded Fourier tests of ANY finite weighted family of actual IBM
averages lie in the common intrinsic domain; no Gaussian observation law. -/
theorem cosine_average_cylinder {I : Type*} [Fintype I] (w t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    ∃ F : JointL2, F ∈ intrinsicCore ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => Real.cos (∑ i, w i * nativeAverage (t i) ω) := by
  obtain ⟨F, hf, ha⟩ := bounded_chain (averageCombination w t) (averageCombination_mem w t ht)
    Real.cos (fun x => -Real.sin x) Real.hasDerivAt_cos Real.continuous_sin.neg 1 1
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)
    (fun x => by simpa only [norm_neg, Real.norm_eq_abs] using Real.abs_sin_le_one x)
  refine ⟨F, hf, ?_⟩
  filter_upwards [ha, averageCombination_ae w t] with ω h1 h2
  rw [h1, h2]

theorem sine_average_cylinder {I : Type*} [Fintype I] (w t : I → ℝ)
    (ht : ∀ i, 0 ≤ t i) :
    ∃ F : JointL2, F ∈ intrinsicCore ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => Real.sin (∑ i, w i * nativeAverage (t i) ω) := by
  obtain ⟨F, hf, ha⟩ := bounded_chain (averageCombination w t) (averageCombination_mem w t ht)
    Real.sin Real.cos Real.hasDerivAt_sin Real.continuous_cos 1 1
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
    (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)
  refine ⟨F, hf, ?_⟩
  filter_upwards [ha, averageCombination_ae w t] with ω h1 h2
  rw [h1, h2]

/-- Ordinary-time recovery puts actual IBM point observations in the L2
closure of the intrinsic common domain; it does NOT put them in the domain. -/
theorem point_mem_core_closure {T : ℝ} (hT : 0 < T) :
    jointRealization (IBMRandomTimeHilbert.randomSourceL2 T.toNNReal) ∈
      intrinsicCore.topologicalClosure := by
  apply intrinsicCore.isClosed_topologicalClosure.mem_of_tendsto
    (nativeAverage_hasDerivAt hT).tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with e he
  exact intrinsicCore.le_topologicalClosure (intrinsicCore.smul_mem _
    (intrinsicCore.sub_mem (nativeAverage_mem (T + e)
        (add_nonneg hT.le (show 0 < e from he).le))
      (nativeAverage_mem T hT.le)))

/-- Closure under bounded C1 composition is a statement about the L2 closure,
with no uniform derivative bound on an approximating sequence required. -/
theorem bounded_chain_closure (f : JointL2) (hf : f ∈ intrinsicCore.topologicalClosure)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : JointL2, F ∈ intrinsicCore.topologicalClosure ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (f ω) := by
  classical
  have hh : f ∈ closure (intrinsicCore : Set JointL2) := hf
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hh
  choose Fn hFn hFa using fun n => bounded_chain (u n) (hu n) φ dφ hd hc A B hA hB
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hB0 : 0 ≤ B := (norm_nonneg (dφ 0)).trans (hB 0)
  have hlip : LipschitzWith ⟨B, hB0⟩ φ :=
    lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt) (fun x => by
      change ‖deriv φ x‖ ≤ B
      rw [(hd x).deriv]
      exact hB x)
  have hm : MemLp (fun ω => φ (f ω)) 2 IBMSourceLaws.jointMeasure :=
    MemLp.of_bound (hφ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) A
      (ae_of_all _ fun ω => hA _)
  let F : JointL2 := hm.toLp _
  have hF : F =ᵐ[IBMSourceLaws.jointMeasure] fun ω => φ (f ω) := hm.coeFn_toLp
  have hconv : Tendsto Fn atTop (𝓝 F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hb (n : ℕ) : ‖Fn n - F‖ ≤ B * ‖u n - f‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hFa n, hF, Lp.coeFn_sub (Fn n) F, Lp.coeFn_sub (u n) f]
        with ω h1 h2 h3 h4
      simp only [h3, Pi.sub_apply, h1, h2, h4]
      exact hlip.norm_sub_le _ _
    apply squeeze_zero (fun n => norm_nonneg _) hb
    simpa using tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp ht)
  exact ⟨F, intrinsicCore.isClosed_topologicalClosure.mem_of_tendsto hconv
    (Eventually.of_forall fun n => intrinsicCore.le_topologicalClosure (hFn n)), hF⟩

/-- Orthogonality to the common intrinsic domain annihilates both real Fourier
channels of every finite family of actual averages. -/
theorem annihilator_average_fourier_moments {I : Type*} [Fintype I]
    (H : JointL2) (hH : H ∈ intrinsicCoreᗮ) (w t : I → ℝ) (ht : ∀ i, 0 ≤ t i) :
    (∫ ω, H ω * Real.cos (∑ i, w i * nativeAverage (t i) ω) ∂IBMSourceLaws.jointMeasure) = 0 ∧
    (∫ ω, H ω * Real.sin (∑ i, w i * nativeAverage (t i) ω) ∂IBMSourceLaws.jointMeasure) = 0 := by
  have htest (v : IBMSourceLaws.JointSample → ℝ)
      (hv : ∃ F : JointL2, F ∈ intrinsicCore ∧ F =ᵐ[IBMSourceLaws.jointMeasure] v) :
      (∫ ω, H ω * v ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    obtain ⟨F, hf, ha⟩ := hv
    have hz := intrinsicCore.inner_left_of_mem_orthogonal hf hH
    rw [L2.inner_def] at hz
    calc
      _ = ∫ ω, inner ℝ (H ω) (F ω) ∂IBMSourceLaws.jointMeasure := by
        apply integral_congr_ae
        filter_upwards [ha] with ω hω
        rw [hω]
        simp [RCLike.inner_apply, mul_comm]
      _ = 0 := hz
  exact ⟨htest _ (cosine_average_cylinder w t ht), htest _ (sine_average_cylinder w t ht)⟩

/-- Finite nonlinear point-observation tests are in the L2 closure of the
actual intrinsic common domain. Positive times avoid a separate zero-time
normalization lemma; no point derivative-domain assertion is made. -/
theorem point_cylinder_closure {I : Type*} [Fintype I] (w t : I → ℝ)
    (ht : ∀ i, 0 < t i)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : JointL2, F ∈ intrinsicCore.topologicalClosure ∧
      F =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
        φ (∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω) := by
  classical
  let q : JointL2 := ∑ i, w i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal)
  have hq : q ∈ intrinsicCore.topologicalClosure :=
    intrinsicCore.topologicalClosure.sum_mem (fun i _ =>
      intrinsicCore.topologicalClosure.smul_mem (w i) (point_mem_core_closure (ht i)))
  have hqa : q =ᵐ[IBMSourceLaws.jointMeasure] fun ω =>
      ∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
        w i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal)),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (w i)
        (jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal))),
      ae_all_iff.mpr (fun i => joint_point_actual_ae (t i).toNNReal)] with ω hs hm hp
    change (∑ i, w i • jointRealization (IBMRandomTimeHilbert.randomSourceL2 (t i).toNNReal)) ω = _
    rw [hs]
    simp only [Finset.sum_apply, hm, Pi.smul_apply, smul_eq_mul, hp]
  obtain ⟨F, hf, ha⟩ := bounded_chain_closure q hq φ dφ hd hc A B hA hB
  refine ⟨F, hf, ?_⟩
  filter_upwards [ha, hqa] with ω h1 h2
  rw [h1, h2]

/-- The annihilator has zero sine and cosine moments against finite ACTUAL
IBM point observations. This is the finite-dimensional Fourier input to a
nonGaussian density proof, not yet the uniqueness/density conclusion. -/
theorem annihilator_point_fourier_moments {I : Type*} [Fintype I]
    (H : JointL2) (hH : H ∈ intrinsicCoreᗮ) (w t : I → ℝ) (ht : ∀ i, 0 < t i) :
    (∫ ω, H ω * Real.cos (∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω)
      ∂IBMSourceLaws.jointMeasure) = 0 ∧
    (∫ ω, H ω * Real.sin (∑ i, w i * IBMConstructedSources.ibmValue (t i).toNNReal ω)
      ∂IBMSourceLaws.jointMeasure) = 0 := by
  have hHc : H ∈ intrinsicCore.topologicalClosureᗮ := by
    rwa [Submodule.orthogonal_closure]
  have htest (v : IBMSourceLaws.JointSample → ℝ)
      (hv : ∃ F : JointL2, F ∈ intrinsicCore.topologicalClosure ∧
        F =ᵐ[IBMSourceLaws.jointMeasure] v) :
      (∫ ω, H ω * v ω ∂IBMSourceLaws.jointMeasure) = 0 := by
    obtain ⟨F, hf, ha⟩ := hv
    have hz := intrinsicCore.topologicalClosure.inner_left_of_mem_orthogonal hf hHc
    rw [L2.inner_def] at hz
    calc
      _ = ∫ ω, inner ℝ (H ω) (F ω) ∂IBMSourceLaws.jointMeasure := by
        apply integral_congr_ae
        filter_upwards [ha] with ω hω
        rw [hω]
        simp [RCLike.inner_apply, mul_comm]
      _ = 0 := hz
  constructor
  · apply htest
    exact point_cylinder_closure w t ht Real.cos (fun x => -Real.sin x)
      Real.hasDerivAt_cos Real.continuous_sin.neg 1 1
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)
      (fun x => by simpa only [norm_neg, Real.norm_eq_abs] using Real.abs_sin_le_one x)
  · apply htest
    exact point_cylinder_closure w t ht Real.sin Real.cos
      Real.hasDerivAt_sin Real.continuous_cos 1 1
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one x)
      (fun x => by simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one x)

end OperatorDerivativeRewrite.Foundation.IBMFiniteAverageCore
