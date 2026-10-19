import Foundation.GaussianFiniteGradientTransport
import Foundation.BochnerL2Approximation
import Foundation.ProductL2Equivalence

/-! Strong multiplier limits and analytic chain calculus for the actual closed
Gaussian derivative, rather than only its polynomial cylindrical core. -/
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.GaussianClosedChainRule
open InfiniteGaussian
attribute [local instance] GaussianProductDerivative.coefficientSpace_secondCountable
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by simp⟩
set_option backward.isDefEq.respectTransparency false

theorem multiplier_memLp (a : SampleSpace → ℝ) (ha : AEStronglyMeasurable a gaussianProduct)
    (B : ℝ) (hb : ∀ᵐ ω ∂gaussianProduct, ‖a ω‖ ≤ B) (g : GaussianVectorL2) :
    MemLp (fun ω => a ω • g ω) 2 gaussianProduct :=
  smul_memLp (p := ∞) (q := 2) (r := 2) (MemLp.of_bound ha B hb) (Lp.memLp g)

def multiplier (a : SampleSpace → ℝ) (ha : AEStronglyMeasurable a gaussianProduct)
    (B : ℝ) (hb : ∀ᵐ ω ∂gaussianProduct, ‖a ω‖ ≤ B) (g : GaussianVectorL2) : GaussianVectorL2 :=
  (multiplier_memLp a ha B hb g).toLp _

theorem multiplier_ae (a : SampleSpace → ℝ) (ha : AEStronglyMeasurable a gaussianProduct)
    (B : ℝ) (hb : ∀ᵐ ω ∂gaussianProduct, ‖a ω‖ ≤ B) (g : GaussianVectorL2) :
    multiplier a ha B hb g =ᵐ[gaussianProduct] fun ω => a ω • g ω :=
  (multiplier_memLp a ha B hb g).coeFn_toLp

theorem multiplier_sub_bound (a : SampleSpace → ℝ)
    (ha : AEStronglyMeasurable a gaussianProduct) (B : ℝ)
    (hb : ∀ᵐ ω ∂gaussianProduct, ‖a ω‖ ≤ B) (g h : GaussianVectorL2) :
    ‖multiplier a ha B hb g - multiplier a ha B hb h‖ ≤ B * ‖g - h‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [multiplier_ae a ha B hb g, multiplier_ae a ha B hb h, hb,
    Lp.coeFn_sub (multiplier a ha B hb g) (multiplier a ha B hb h), Lp.coeFn_sub g h]
    with ω hg hh hb hs hd
  simp only [hs, Pi.sub_apply, hg, hh, hd, ← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

theorem multiplier_tendsto_fixed (a : ℕ → SampleSpace → ℝ) (b : SampleSpace → ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) gaussianProduct)
    (hb : AEStronglyMeasurable b gaussianProduct) (B : ℝ) (hB : 0 ≤ B)
    (hba : ∀ n, ∀ᵐ ω ∂gaussianProduct, ‖a n ω‖ ≤ B)
    (hbb : ∀ᵐ ω ∂gaussianProduct, ‖b ω‖ ≤ B)
    (ht : ∀ᵐ ω ∂gaussianProduct, Tendsto (fun n => a n ω) atTop (𝓝 (b ω)))
    (g : GaussianVectorL2) :
    Tendsto (fun n => multiplier (a n) (ha n) B (hba n) g) atTop
      (𝓝 (multiplier b hb B hbb g)) := by
  let hm := (Lp.memLp g).norm.const_mul B
  let m : Lp ℝ 2 gaussianProduct := hm.toLp (fun ω => B * ‖g ω‖)
  apply BochnerL2Approximation.tendsto_of_dominated _ _ m
  · intro n
    filter_upwards [multiplier_ae (a n) (ha n) B (hba n) g, hm.coeFn_toLp, hba n]
      with ω ha hm hb
    rw [ha, hm, norm_smul, Real.norm_of_nonneg (mul_nonneg hB (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · filter_upwards [multiplier_ae b hb B hbb g, hm.coeFn_toLp, hbb] with ω ha hm hb
    rw [ha, hm, norm_smul, Real.norm_of_nonneg (mul_nonneg hB (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · filter_upwards [ht, ae_all_iff.mpr (fun n => multiplier_ae (a n) (ha n) B (hba n) g),
      multiplier_ae b hb B hbb g] with ω ht ha hb
    simpa only [ha, hb] using ht.smul_const (g ω)

theorem multiplier_tendsto (a : ℕ → SampleSpace → ℝ) (b : SampleSpace → ℝ)
    (ha : ∀ n, AEStronglyMeasurable (a n) gaussianProduct)
    (hb : AEStronglyMeasurable b gaussianProduct) (B : ℝ) (hB : 0 ≤ B)
    (hba : ∀ n, ∀ᵐ ω ∂gaussianProduct, ‖a n ω‖ ≤ B)
    (hbb : ∀ᵐ ω ∂gaussianProduct, ‖b ω‖ ≤ B)
    (ht : ∀ᵐ ω ∂gaussianProduct, Tendsto (fun n => a n ω) atTop (𝓝 (b ω)))
    (g : ℕ → GaussianVectorL2) (h : GaussianVectorL2) (hg : Tendsto g atTop (𝓝 h)) :
    Tendsto (fun n => multiplier (a n) (ha n) B (hba n) (g n)) atTop
      (𝓝 (multiplier b hb B hbb h)) := by
  have hf := multiplier_tendsto_fixed a b ha hb B hB hba hbb ht h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun n => B * ‖g n - h‖ +
      ‖multiplier (a n) (ha n) B (hba n) h - multiplier b hb B hbb h‖) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hg)).add
      (tendsto_iff_norm_sub_tendsto_zero.mp hf))
  apply squeeze_zero (fun n => norm_nonneg _) _ hz
  intro n
  exact (norm_sub_le_norm_sub_add_norm_sub (multiplier (a n) (ha n) B (hba n) (g n))
    (multiplier (a n) (ha n) B (hba n) h) (multiplier b hb B hbb h)).trans
      (add_le_add (multiplier_sub_bound (a n) (ha n) B (hba n) (g n) h) le_rfl)

/-- The actual polynomial operator core approximates both coordinates of every
closed derivative graph point. -/
theorem core_graph_sequence (f : GaussianL2) (g : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph) :
    ∃ u : ℕ → polynomialCylindricalDomain,
      Tendsto (fun n => ((u n : GaussianL2), polynomialDerivative (u n))) atTop (𝓝 (f, g)) := by
  have hh : (f, g) ∈ closure (cylindricalDerivative.graph : Set (GaussianL2 × GaussianVectorL2)) := by
    rw [closedCylindricalDerivative_graph] at hfg
    exact hfg
  obtain ⟨z, hz, ht⟩ := mem_closure_iff_seq_limit.mp hh
  let u : ℕ → polynomialCylindricalDomain := fun n =>
    ⟨(z n).1, LinearPMap.mem_domain_of_mem_graph (hz n)⟩
  refine ⟨u, ?_⟩
  have he (n : ℕ) : ((u n : GaussianL2), polynomialDerivative (u n)) = z n := by
    apply Prod.ext
    · rfl
    · exact ((cylindricalDerivative.image_iff (u n).2).mpr (hz n)).symm
  simpa only [he] using ht

/-- Bounded C1 chain rule on the full existing closed Gaussian Sobolev domain.
Both actual random fields and their original derivative graph are identified. -/
theorem bounded_closed_chain_graph (f : GaussianL2) (g : GaussianVectorL2)
    (hfg : (f, g) ∈ closedCylindricalDerivative.graph)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : GaussianL2, ∃ G : GaussianVectorL2,
      (F, G) ∈ closedCylindricalDerivative.graph ∧
      F =ᵐ[gaussianProduct] (fun ω => φ (f ω)) ∧
      G =ᵐ[gaussianProduct] (fun ω => dφ (f ω) • g ω) := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg (dφ 0)).trans (hB 0)
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hlip : LipschitzWith ⟨B, hB0⟩ φ :=
    lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt)
      (fun x => by
        change ‖deriv φ x‖ ≤ B
        rw [(hd x).deriv]
        exact hB x)
  obtain ⟨u, hu⟩ := core_graph_sequence f g hfg
  have huf := hu.fst_nhds
  have hug := hu.snd_nhds
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp huf).exists_seq_tendsto_ae
  choose Fn Gn hgraph hFn hGn using fun n =>
    GaussianFiniteGradientTransport.bounded_core_chain_graph (u (ns n)) φ dφ hd hc A B hA hB
  have hf : MemLp (fun ω => φ (f ω)) 2 gaussianProduct :=
    MemLp.of_bound (hφ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) A
      (ae_of_all _ fun ω => hA _)
  let F : GaussianL2 := hf.toLp _
  have hF : F =ᵐ[gaussianProduct] fun ω => φ (f ω) := hf.coeFn_toLp
  let a : ℕ → SampleSpace → ℝ := fun n ω => dφ ((u (ns n) : GaussianL2) ω)
  let b : SampleSpace → ℝ := fun ω => dφ (f ω)
  have ha : ∀ n, AEStronglyMeasurable (a n) gaussianProduct := fun n =>
    hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable (u (ns n) : GaussianL2))
  have hb : AEStronglyMeasurable b gaussianProduct :=
    hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)
  have hba : ∀ n, ∀ᵐ ω ∂gaussianProduct, ‖a n ω‖ ≤ B := fun n => ae_of_all _ fun ω => hB _
  have hbb : ∀ᵐ ω ∂gaussianProduct, ‖b ω‖ ≤ B := ae_of_all _ fun ω => hB _
  let G := multiplier b hb B hbb g
  have hFt : Tendsto Fn atTop (𝓝 F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hbound (n : ℕ) : ‖Fn n - F‖ ≤ B * ‖(u (ns n) : GaussianL2) - f‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [hFn n, hF, Lp.coeFn_sub (Fn n) F,
        Lp.coeFn_sub (u (ns n) : GaussianL2) f] with ω hn hf hs hu
      simp only [hs, Pi.sub_apply, hn, hf, hu]
      exact hlip.norm_sub_le _ _
    apply squeeze_zero (fun n => norm_nonneg _) hbound
    simpa using tendsto_const_nhds.mul
      (tendsto_iff_norm_sub_tendsto_zero.mp (huf.comp hns.tendsto_atTop))
  have hGt : Tendsto Gn atTop (𝓝 G) := by
    have he (n : ℕ) : Gn n = multiplier (a n) (ha n) B (hba n) (polynomialDerivative (u (ns n))) := by
      apply Lp.ext
      exact (hGn n).trans (multiplier_ae (a n) (ha n) B (hba n) _).symm
    rw [show Gn = (fun n => multiplier (a n) (ha n) B (hba n)
      (polynomialDerivative (u (ns n)))) from funext he]
    apply multiplier_tendsto a b ha hb B hB0 hba hbb _ _ g (hug.comp hns.tendsto_atTop)
    filter_upwards [hae] with ω hω
    exact hc.continuousAt.tendsto.comp hω
  refine ⟨F, G, closedCylindricalDerivative_isClosed.mem_of_tendsto
    (hFt.prodMk_nhds hGt) (Eventually.of_forall hgraph), hf.coeFn_toLp, ?_⟩
  exact multiplier_ae b hb B hbb g

/-- The chain rule acts in actual Gaussian product sections. The transformed
gradient is constructed globally in product L2, so no measurable selection of
fiberwise derivative witnesses is assumed. -/
theorem bounded_product_chain_graph
    (f : Lp ℝ 2 (gaussianProduct.prod gaussianProduct))
    (g : Lp CoefficientSpace 2 (gaussianProduct.prod gaussianProduct))
    (hfg : (ProductL2Curry.curry gaussianProduct gaussianProduct f,
      ProductL2Curry.curry gaussianProduct gaussianProduct g) ∈
        (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph)
    (φ dφ : ℝ → ℝ) (hd : ∀ x, HasDerivAt φ (dφ x) x) (hc : Continuous dφ)
    (A B : ℝ) (hA : ∀ x, ‖φ x‖ ≤ A) (hB : ∀ x, ‖dφ x‖ ≤ B) :
    ∃ F : Lp ℝ 2 (gaussianProduct.prod gaussianProduct),
    ∃ G : Lp CoefficientSpace 2 (gaussianProduct.prod gaussianProduct),
      (ProductL2Curry.curry gaussianProduct gaussianProduct F,
        ProductL2Curry.curry gaussianProduct gaussianProduct G) ∈
          (BochnerClosedOperator.lift gaussianProduct closedCylindricalDerivative).graph ∧
      F =ᵐ[gaussianProduct.prod gaussianProduct] (fun ω => φ (f ω)) ∧
      G =ᵐ[gaussianProduct.prod gaussianProduct] (fun ω => dφ (f ω) • g ω) := by
  have hφ : Continuous φ := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hf : MemLp (fun ω => φ (f ω)) 2 (gaussianProduct.prod gaussianProduct) :=
    MemLp.of_bound (hφ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) A
      (ae_of_all _ fun ω => hA _)
  have ha : MemLp (fun ω => dφ (f ω)) ∞ (gaussianProduct.prod gaussianProduct) :=
    MemLp.of_bound (hc.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) B
      (ae_of_all _ fun ω => hB _)
  have hg : MemLp (fun ω => dφ (f ω) • g ω) 2 (gaussianProduct.prod gaussianProduct) :=
    smul_memLp (p := ∞) (q := 2) (r := 2) ha (Lp.memLp g)
  let F := hf.toLp _
  let G := hg.toLp _
  have hF : F =ᵐ[gaussianProduct.prod gaussianProduct] fun ω => φ (f ω) := hf.coeFn_toLp
  have hG : G =ᵐ[gaussianProduct.prod gaussianProduct] fun ω => dφ (f ω) • g ω := hg.coeFn_toLp
  refine ⟨F, G, ?_, hF, hG⟩
  rw [BochnerClosedOperator.mem_lift_graph_iff] at hfg ⊢
  filter_upwards [hfg, ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct f,
    ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct g,
    ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct F,
    ProductL2Curry.curry_coeFn gaussianProduct gaussianProduct G,
    ae_ae_of_ae_prod hF, ae_ae_of_ae_prod hG] with x hx hf hg hF hG hFj hGj
  obtain ⟨Fx, Gx, hxg, hFx, hGx⟩ := bounded_closed_chain_graph _ _ hx φ dφ hd hc A B hA hB
  have heF : ProductL2Curry.curry gaussianProduct gaussianProduct F x = Fx := by
    apply Lp.ext
    filter_upwards [hF, hFj, hf, hFx] with y h1 h2 h3 h4
    rw [h1, h2, h4, h3]
  have heG : ProductL2Curry.curry gaussianProduct gaussianProduct G x = Gx := by
    apply Lp.ext
    filter_upwards [hG, hGj, hf, hg, hGx] with y h1 h2 h3 h4 h5
    rw [h1, h2, h5, h3, h4]
  rwa [heF, heG]

end OperatorDerivativeRewrite.Foundation.GaussianClosedChainRule
