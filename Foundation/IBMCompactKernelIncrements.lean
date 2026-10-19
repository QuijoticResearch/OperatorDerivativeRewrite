import Foundation.IBMCompactKernelSchwartz
import Foundation.IBMUniformMollifiedIncrements

/-! All positive normalized compact kernels contract the same Brownian spatial
increments. No derivative norm of the kernel enters the estimate. -/
noncomputable section
open MeasureTheory Set
namespace OperatorDerivativeRewrite.Foundation.IBMCompactKernelIncrements
open InfiniteGaussian IBMContinuousScenery IBMContinuousBulkVariance IBMCompactKernelSchwartz
set_option backward.isDefEq.respectTransparency false

theorem scenery_increment (ρ : ℝ → ℝ) (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (r s : ℝ) :
    ‖wholeLineScenery ρ r-wholeLineScenery ρ s‖ ≤ Real.sqrt |r-s| := by
  obtain ⟨R0,hR0⟩ := hc.isBounded.exists_norm_le
  let R := max R0 0
  have hR : 0 ≤ R := le_max_right _ _
  have hs (z : ℝ) (hz : ρ z ≠ 0) : |z| ≤ R := by
    have hb : |z| ≤ R0 := by
      simpa only [Real.norm_eq_abs] using hR0 z (subset_tsupport ρ hz)
    exact hb.trans (le_max_left _ _)
  have he (x : ℝ) : wholeLineScenery ρ x = offsetScenery (-R) R x ρ := by
    apply IBMOffsetTranslation.wholeLineScenery_eq_offsetScenery
    · linarith
    · intro u hu
      by_contra hz
      have hb := abs_le.mp (hs (x-u) hz)
      exact hu ⟨by linarith,by linarith⟩
  rw [he r,he s,offsetScenery_eq_integral,offsetScenery_eq_integral]
  have hi (x : ℝ) : IntegrableOn (fun u : ℝ => ρ (-u) • sourceScenery (x+u))
      (Icc (-R) R) volume :=
    ((hρ.comp continuous_neg).smul
      (sourceScenery_continuous.comp (continuous_const.add continuous_id))).integrableOn_Icc
  rw [← integral_sub (hi r) (hi s)]
  have hmajor : IntegrableOn (fun u : ℝ => ρ (-u)*Real.sqrt |r-s|) (Icc (-R) R) volume :=
    ((hρ.comp continuous_neg).mul continuous_const).integrableOn_Icc
  have hb : ∀ᵐ u ∂volume.restrict (Icc (-R) R),
      ‖ρ (-u) • sourceScenery (r+u)-ρ (-u) • sourceScenery (s+u)‖ ≤
        ρ (-u)*Real.sqrt |r-s| := by
    apply ae_of_all
    intro u
    rw [← smul_sub,norm_smul,Real.norm_of_nonneg (hpos _),
      IBMUniformMollifiedIncrements.scenery_increment_norm]
    simp only [add_sub_add_right_eq_sub]
    exact le_rfl
  apply (norm_integral_le_of_norm_le hmajor hb).trans_eq
  have hm : (∫ u in Icc (-R) R, ρ (-u)) = 1 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => ?_)]
    · simpa only [zero_sub] using (integral_sub_left_eq_self ρ volume 0).trans hmass
    · by_contra hz
      have hb := abs_le.mp (by simpa only [abs_neg] using hs (-u) hz)
      exact hu hb
  rw [integral_mul_const,hm,one_mul]

theorem spatial_increment (g : SchwartzMap ℝ ℝ) (a : ℝ) {ρ : ℝ → ℝ}
    (hc : HasCompactSupport ρ) (hρ : Continuous ρ)
    (hpos : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1) (r s : ℝ) :
    ‖spatial g a ρ r-spatial g a ρ s‖ ≤
      (Real.toNNReal (SchwartzMap.seminorm ℝ 0 1 (IBMCorrectionStein.jet g 0)) : ℝ)*
        Real.sqrt |r-s| := by
  apply (IBMUniformMollifiedIncrements.observable_difference_norm g a 0 _ _).trans
  have he : ‖coefficient ρ r-coefficient ρ s‖ =
      ‖wholeLineScenery ρ r-wholeLineScenery ρ s‖ := by
    rw [← firstChaosEmbedding.norm_map,map_sub,coefficient_embedding,coefficient_embedding]
  rw [he]
  exact mul_le_mul_of_nonneg_left (scenery_increment ρ hc hρ hpos hmass r s) (by positivity)

end OperatorDerivativeRewrite.Foundation.IBMCompactKernelIncrements
