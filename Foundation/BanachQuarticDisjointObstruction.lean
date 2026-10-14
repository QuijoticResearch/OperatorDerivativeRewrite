import Foundation.BanachQuarticInverseObstruction
import Foundation.PoissonDifferenceOperators

/-! Disjoint source images retain cubic inverse singularities away from zero. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace OperatorDerivativeRewrite.Foundation.BanachQuarticDisjointObstruction
open BanachLpDualityFour BanachLpDualityFourInfinite BanachQuarticInverseObstruction
variable {Ω H : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
private instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

theorem dualityFour_disjoint_add (F G : Lp ℝ 4 μ)
    (hd : ∀ᵐ ω ∂μ, F ω*G ω=0) (a : ℝ) :
    dualityFour (F+a • G)=dualityFour F+a^3 • dualityFour G := by
  apply Lp.ext
  filter_upwards [hd,dualityFour_ae (F+a • G),dualityFour_ae F,dualityFour_ae G,
    Lp.coeFn_add F (a • G),Lp.coeFn_smul a G,
    Lp.coeFn_add (dualityFour F) (a^3 • dualityFour G),
    Lp.coeFn_smul (a^3) (dualityFour G)] with ω hd h1 hF hG ha hs hb ht
  rw [h1,ha,hb]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hs,ht,hF,hG]
  rcases mul_eq_zero.mp hd with h | h <;> rw [h] <;> ring

theorem normalFour_disjoint_add (δ : H →L[ℝ] Lp ℝ 4 μ) (u v : H)
    (hd : ∀ᵐ ω ∂μ, δ u ω*δ v ω=0) (a : ℝ) :
    normalFour δ (u+a • v)=normalFour δ u+a^3 • normalFour δ v := by
  simp only [normalFour,map_add,map_smul,dualityFour_disjoint_add _ _ hd a]

variable [CompleteSpace H]

theorem no_local_linear_bound_at_disjoint_image (δ : H →L[ℝ] Lp ℝ 4 μ)
    (c : ℝ) (hc : 0 < c) (hδ : ∀ u : H, c*‖u‖ ≤ ‖δ u‖) (u v : H) (hv : v≠0)
    (hd : ∀ᵐ ω ∂μ, δ u ω*δ v ω=0) (K r : ℝ) (hr : 0 < r) :
    ∃ f : StrongDual ℝ H, ‖f-normalFour δ u‖ < r ∧
      K*‖f-normalFour δ u‖ < ‖(normalFourEquiv δ c hc hδ).symm f-
        (normalFourEquiv δ c hc hδ).symm (normalFour δ u)‖ := by
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht1 : Tendsto (fun a : ℝ => a^3*‖normalFour δ v‖)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => a^3*‖normalFour δ v‖) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left
      (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have ht2 : Tendsto (fun a : ℝ => K*a^2*‖normalFour δ v‖)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => K*a^2*‖normalFour δ v‖) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left
      (show nhdsWithin 0 (Set.Ioi 0) ≤ 𝓝 (0 : ℝ) from inf_le_left)
  have hpos : ∀ᶠ a : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < a := self_mem_nhdsWithin
  obtain ⟨a,ha,hsmall,hlinear⟩ :=
    (hpos.and ((ht1.eventually (eventually_lt_nhds hr)).and
      (ht2.eventually (eventually_lt_nhds hvp)))).exists
  refine ⟨normalFour δ (u+a • v), ?_, ?_⟩
  · rw [normalFour_disjoint_add δ u v hd,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos (pow_pos ha 3)]
    exact hsmall
  · rw [inverse_normalFour,inverse_normalFour,add_sub_cancel_left,norm_smul,
      Real.norm_eq_abs,abs_of_pos ha,normalFour_disjoint_add δ u v hd,
      add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos (pow_pos ha 3)]
    have hm := mul_lt_mul_of_pos_left hlinear ha
    nlinarith [hm]

def poissonAtom (rate : ℝ≥0) (n : ℕ) : Lp ℝ 4 (PoissonDifferenceCore.poissonLaw rate) :=
  indicatorConstLp 4 (measurableSet_singleton n) (by finiteness) (1 : ℝ)

theorem poissonAtom_ne_zero (rate : ℝ≥0) (hr : 0 < rate) (n : ℕ) :
    poissonAtom rate n≠0 := by
  apply norm_pos_iff.mp
  rw [poissonAtom,norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one,one_mul]
  exact Real.rpow_pos_of_pos (PoissonDifferenceCore.poisson_weight_pos rate hr n) _

theorem poissonAtoms_disjoint (rate : ℝ≥0) (n m : ℕ) (hnm : n≠m) :
    ∀ᵐ k ∂PoissonDifferenceCore.poissonLaw rate, poissonAtom rate n k*poissonAtom rate m k=0 := by
  filter_upwards [indicatorConstLp_coeFn (μ := PoissonDifferenceCore.poissonLaw rate)
      (p := 4) (hs := measurableSet_singleton n) (hμs := by finiteness) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (μ := PoissonDifferenceCore.poissonLaw rate)
      (p := 4) (hs := measurableSet_singleton m) (hμs := by finiteness) (c := (1 : ℝ))] with k hn hm
  change poissonAtom rate n k= _ at hn
  change poissonAtom rate m k= _ at hm
  rw [hn,hm]
  by_cases hk : k=n
  · subst k
    simp [hnm]
  · simp [hk]

theorem actual_poisson_nonzero_datum_obstruction (rate : ℝ≥0) (hr : 0 < rate) :
    ∃ u : Lp ℝ 4 (PoissonDifferenceCore.poissonLaw rate),
      normalFour (ContinuousLinearMap.id ℝ _) u≠0 ∧
      ∀ (K r : ℝ), 0 < r → ∃ f : StrongDual ℝ (Lp ℝ 4 (PoissonDifferenceCore.poissonLaw rate)),
        ‖f-normalFour (ContinuousLinearMap.id ℝ _) u‖ < r ∧
          K*‖f-normalFour (ContinuousLinearMap.id ℝ _) u‖ <
            ‖(normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
              (by intro v; simp)).symm f-
              (normalFourEquiv (ContinuousLinearMap.id ℝ _) 1 (by norm_num)
                (by intro v; simp)).symm (normalFour (ContinuousLinearMap.id ℝ _) u)‖ := by
  refine ⟨poissonAtom rate 0, ?_, ?_⟩
  · intro hz
    have he : normalFour (ContinuousLinearMap.id ℝ _) (poissonAtom rate 0)=
        normalFour (ContinuousLinearMap.id ℝ _) 0 := by rw [normalFour_zero]; exact hz
    exact poissonAtom_ne_zero rate hr 0
      (BanachLpDualityFourContinuity.normalFour_injective (ContinuousLinearMap.id ℝ _)
        1 (by norm_num) (by intro v; simp) he)
  · intro K r hR
    exact no_local_linear_bound_at_disjoint_image (ContinuousLinearMap.id ℝ _) 1
      (by norm_num) (by intro v; simp) (poissonAtom rate 0) (poissonAtom rate 1)
      (poissonAtom_ne_zero rate hr 1) (poissonAtoms_disjoint rate 0 1 (by norm_num)) K r hR

end OperatorDerivativeRewrite.Foundation.BanachQuarticDisjointObstruction
