import Foundation.IBMPhysicalNegativeEmbedding
import Foundation.IBMClockNativeSpatial

/-! Spatial H^-1 convergence does not extend the actual scenery white-noise
integral. The actual mollifiers converge to a Dirac mass in H^-1, while their
white-noise images cannot converge in the original Gaussian L2 space. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology BesselPotentialSpace
namespace OperatorDerivativeRewrite.Foundation.IBMPhysicalWhiteNoiseObstruction
open GaussianTimeHilbert InfiniteGaussian IBMPhysicalNoiseVectors
open IBMPhysicalNoiseRealization IBMPhysicalNoiseCalculus

def profile (n : ℕ) : TimeHilbert :=
  IBMPhysicalDerivativeKernel.translatedClass (IBMMollifier.kernel n)
    (IBMMollifier.kernel_smooth n).continuous (IBMMollifier.kernel_compactSupport n) 0

def probe (n : ℕ) : TimeHilbert :=
  intervalVector (-(IBMMollifier.bump n).rOut) (IBMMollifier.bump n).rOut

theorem probe_tendsto : Tendsto probe atTop (nhds 0) := by
  have hn : Tendsto (fun n => -(IBMMollifier.bump n).rOut) atTop (nhds 0) := by
    simpa only [neg_zero] using IBMMollifier.bump_outer_tendsto_zero.neg
  have h := (vector_continuous.tendsto 0 |>.comp IBMMollifier.bump_outer_tendsto_zero).sub
    (vector_continuous.tendsto 0 |>.comp hn)
  have he (n : ℕ) : probe n =
      vector (IBMMollifier.bump n).rOut-vector (-(IBMMollifier.bump n).rOut) :=
    (vector_sub (by linarith [(IBMMollifier.bump n).rOut_pos])).symm
  simpa only [Function.comp_def, ← he, vector_zero, sub_self, neg_zero] using h

theorem probe_profile_pairing (n : ℕ) : inner ℝ (probe n) (profile n) = 1 := by
  rw [L2_inner_eq_integral]
  have he : (fun x => inner ℝ (probe n x) (profile n x)) =ᵐ[volume]
      fun x => IBMMollifier.kernel n (0-x) := by
    filter_upwards [intervalVector_coeFn (-(IBMMollifier.bump n).rOut)
      (IBMMollifier.bump n).rOut,
      IBMPhysicalDerivativeKernel.translatedClass_coeFn (IBMMollifier.kernel n)
        (IBMMollifier.kernel_smooth n).continuous
        (IBMMollifier.kernel_compactSupport n) 0] with x hp hk
    change probe n x = _ at hp
    change profile n x = _ at hk
    rw [hp, hk, Real.inner_apply]
    by_cases hx : x ∈ Ioc (-(IBMMollifier.bump n).rOut) (IBMMollifier.bump n).rOut
    · simp [hx]
    · have hf : (IBMMollifier.bump n).rOut ≤ |0-x| := by
        simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
        rcases hx with h | h
        · rw [zero_sub, abs_neg]
          exact le_trans (by linarith) (neg_le_abs x)
        · rw [zero_sub, abs_neg]
          exact h.le.trans (le_abs_self x)
      rw [IBMClockNativeSpatial.kernel_zero_of_far n _ hf]
      simp
  rw [integral_congr_ae he, integral_sub_left_eq_self, IBMMollifier.kernel_integral]

theorem profile_hminus_tendsto :
    Tendsto (fun n => IBMPhysicalNegativeEmbedding.embedding (profile n)) atTop
      (nhds (IBMPhysicalDirac.dirac 0)) :=
  IBMPhysicalDirac.translated_tendsto 0

theorem whiteNoise_not_tendsto (G : GaussianL2) :
    ¬ Tendsto (fun n => physicalNoise (profile n)) atTop (nhds G) := by
  intro hG
  have hp := physicalNoise.continuous.tendsto 0 |>.comp probe_tendsto
  have ht := hp.inner (𝕜 := ℝ) hG
  have he (n : ℕ) : inner ℝ (physicalNoise (probe n)) (physicalNoise (profile n)) = 1 := by
    rw [physicalNoise.inner_map_map, probe_profile_pairing]
  have hz : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_def, he, map_zero, inner_zero_left] using ht
  have : (1 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  norm_num at this

theorem whiteNoise_norm_escape :
    Tendsto (fun n => ‖physicalNoise (profile n)‖) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  by_cases hb : b ≤ 0
  · exact Eventually.of_forall fun n => hb.trans (norm_nonneg _)
  have hb' : 0 < b+1 := by linarith
  have hp := (probe_tendsto.norm).eventually (gt_mem_nhds (by
    simpa only [norm_zero] using (one_div_pos.mpr hb')))
  apply hp.mono
  intro n hn
  have hn' : ‖probe n‖*(b+1) < 1 := (lt_div_iff₀ hb').mp hn
  have hi := norm_inner_le_norm (𝕜 := ℝ) (physicalNoise (probe n))
    (physicalNoise (profile n))
  rw [physicalNoise.inner_map_map, probe_profile_pairing, norm_one,
    physicalNoise.norm_map] at hi
  by_contra hh
  have hm := mul_le_mul_of_nonneg_left (lt_of_not_ge hh).le (norm_nonneg (probe n))
  nlinarith

/-- Even a nonlinear map continuous at the Dirac mass cannot agree with the
actual Wiener integral on all ordinary physical L2 kernels. -/
theorem no_continuous_extension :
    ¬ ∃ F : H^{(-1 : ℝ)}(ℝ) → GaussianL2,
      ContinuousAt F (IBMPhysicalDirac.dirac 0) ∧
      ∀ u : TimeHilbert, F (IBMPhysicalNegativeEmbedding.embedding u) = physicalNoise u := by
  rintro ⟨F, hF, hFagree⟩
  apply whiteNoise_not_tendsto (F (IBMPhysicalDirac.dirac 0))
  simpa only [Function.comp_def, hFagree] using hF.tendsto.comp profile_hminus_tendsto

end OperatorDerivativeRewrite.Foundation.IBMPhysicalWhiteNoiseObstruction
