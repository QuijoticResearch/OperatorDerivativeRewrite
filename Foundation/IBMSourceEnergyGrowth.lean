import Foundation.IBMClockGridPath

/-! Actual uniform-grid source energy grows without bound. The geometric
concentration proof uses folded QV, compact clock paths and original L1
subsequences; it assumes no four-time Gaussian lower bound. -/
noncomputable section
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.IBMSourceEnergyGrowth
open InfiniteGaussian IBMRawGridSecondChaos IBMRawGridObservableTests
open IBMUniformClockGridEnergy IBMSpatialClockEnergy IBMClockGridPath
open IBMFoldedClockQuadraticVariation IBMClippedClockStrongLimit

def total (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) : ℝ :=
  ‖sourceGrid (H/(N+1)) (N+1) Y‖^2+clockSquares (H/(N+1)) (N+1) Y

theorem total_nonneg (H : ℝ≥0) (N : ℕ) (Y : SampleSpace) : 0 ≤ total H N Y := by
  apply add_nonneg (sq_nonneg _)
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem total_integrable (H : ℝ≥0) (N : ℕ) : Integrable (total H N) gaussianProduct :=
  ((memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (sourceGrid (H/(N+1)) (N+1)))).mp (Lp.memLp _)).add
      (clockSquares_integrable _ _)

theorem total_mean (H : ℝ≥0) (N : ℕ) :
    (∫ Y, total H N Y ∂gaussianProduct) = ‖sourceGrid (H/(N+1)) (N+1)‖^2+(H:ℝ) := by
  have hi := (memLp_two_iff_integrable_sq_norm
    (Lp.aestronglyMeasurable (sourceGrid (H/(N+1)) (N+1)))).mp (Lp.memLp _)
  unfold total
  rw [integral_add hi (clockSquares_integrable _ _),clockSquares_mean]
  have he : grid (H/(N+1)) (N+1) = H := by
    unfold grid
    have hn : (N+1:ℝ≥0) ≠ 0 := by positivity
    simpa only [Nat.cast_add,Nat.cast_one] using div_mul_cancel₀ H hn
  rw [he]
  congr 1
  rw [← real_inner_self_eq_norm_sq,L2_inner_eq_integral]
  exact integral_congr_ae (ae_of_all _ fun Y => (real_inner_self_eq_norm_sq _).symm)

theorem total_pathwise_escape (H : ℝ≥0) (hH : 0 < H) (Y : SampleSpace)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (hmass : Tendsto (fun j => foldedSum H (k j) Y) atTop (𝓝 (H:ℝ)))
    (hgrid : ∀ N i : ℕ, IBMConstructedSources.clockPath Y (grid (H/(N+1)) i) =
      GaussianTimeProcess.process (grid (H/(N+1)) i) Y)
    (hinit : ∀ N : ℕ, clockCurve (H/(N+1)) Y 0 = 0)
    (hsource : ∀ N : ℕ, sourceGrid (H/(N+1)) (N+1) Y =
      sourceSum (clockCurve (H/(N+1)) Y) (N+1)) :
    Tendsto (fun j => total H (k j) Y) atTop atTop := by
  let f := IBMConstructedSources.clockPath Y
  obtain ⟨M,hM,hbound⟩ := path_bound f H
  let δ : ℕ → ℝ := fun N => pathMesh f H N+1/(N+1:ℝ)
  have hδpos (N : ℕ) : 0 < δ N := by
    exact add_pos_of_nonneg_of_pos (pathMesh_nonneg f H N) (by positivity)
  have hstep : Tendsto (fun N : ℕ => 1/(N+1:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [zero_add] using (pathMesh_tendsto f H).add hstep
  have hc (N : ℕ) : (foldedSum H N Y)^2 ≤ (4*M*δ N)*total H N Y := by
    have he := concentration_source_bound (H/(N+1)) (N+1) Y (hinit N) hM.le (hδpos N).le
      (fun i hi => by
        unfold radius
        rw [← hgrid N i]
        exact hbound _ (grid_mem H N i hi))
      (fun i hi => by
        unfold radius
        rw [← hgrid N (i+1),← hgrid N i]
        exact (abs_abs_sub_abs_le_abs_sub _ _).trans
          ((increment_le_pathMesh f H N i hi).trans (le_add_of_nonneg_right (by positivity))))
    rw [uniform_mass,← hsource N] at he
    exact he
  apply tendsto_atTop.mpr
  intro b
  let L := max b 0+1
  have hL : 0 < L := by dsimp [L]; positivity
  have hbL : b ≤ L := by dsimp [L]; linarith [le_max_left b 0]
  have htol : 0 < (H:ℝ)^2/(16*M*L) := div_pos (sq_pos_of_pos hH) (by positivity)
  filter_upwards [hmass.eventually (lt_mem_nhds (by linarith : (H:ℝ)/2 < H)),
    (hδ.comp hk).eventually (gt_mem_nhds htol)] with j hm hd
  by_contra hh
  have hb : total H (k j) Y ≤ L := (le_of_not_ge hh).trans hbL
  have he := (hc (k j)).trans (mul_le_mul_of_nonneg_left hb (mul_nonneg (mul_nonneg (by norm_num) hM.le) (hδpos _).le))
  have hsmall := (lt_div_iff₀ (show 0 < 16*M*L by positivity)).mp hd
  have hs := mul_self_lt_mul_self (show (0:ℝ) ≤ (H:ℝ)/2 by positivity) hm
  change δ (k j) * (16*M*L) < (H:ℝ)^2 at hsmall
  nlinarith only [he,hsmall,hs]

theorem source_energy_tendsto_atTop (H : ℝ≥0) (hH : 0 < H) :
    Tendsto (fun N : ℕ => ‖sourceGrid (H/(N+1)) (N+1)‖^2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  by_contra hbad
  simp only [Filter.eventually_atTop] at hbad
  push_neg at hbad
  choose k hk hkb using hbad
  have hkt : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hlp := (foldedClass_tendsto H hH).comp hkt
  obtain ⟨s,hs,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hlp).exists_seq_tendsto_ae
  have hm : Tendsto (fun j => k (s j)) atTop atTop := hkt.comp hs.tendsto_atTop
  have hconstant : clockL1 ((H:ℝ) • gaussianOne) =ᵐ[gaussianProduct] fun _ => (H:ℝ) := by
    filter_upwards [clockL1_actual ((H:ℝ) • gaussianOne),Lp.coeFn_smul (H:ℝ) (gaussianOne:GaussianL2),
      gaussianOne_coeFn] with Y hl hc h1
    rw [hl,hc,Pi.smul_apply,h1,smul_eq_mul,mul_one]
  have he : ∀ᵐ Y ∂gaussianProduct, Tendsto (fun j => total H (k (s j)) Y) atTop atTop := by
    filter_upwards [hlim,hconstant,clock_grid_ae H,
      ae_all_iff.mpr (fun N : ℕ => clockCurve_initial (H/(N+1))),
      ae_all_iff.mpr (fun N : ℕ => sourceGrid_ae (H/(N+1)) (N+1)),
      ae_all_iff.mpr (fun N : ℕ => foldedClass_actual H N)] with Y hf hc hg hi ha hfold
    have hmass : Tendsto (fun j => foldedSum H (k (s j)) Y) atTop (𝓝 (H:ℝ)) := by
      rw [hc] at hf
      exact hf.congr' (Eventually.of_forall fun j => hfold (k (s j)))
    exact total_pathwise_escape H hH Y (fun j => k (s j)) hm hmass hg hi ha
  let R : ℝ := max (C+(H:ℝ)) 0+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hmeas (j : ℕ) : AEStronglyMeasurable (fun Y => min (total H (k (s j)) Y) R) gaussianProduct :=
    ((total_integrable H _).aestronglyMeasurable.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hdom (j : ℕ) : ∀ᵐ Y ∂gaussianProduct, ‖min (total H (k (s j)) Y) R‖ ≤ R := by
    exact ae_of_all _ fun Y => by
      rw [Real.norm_of_nonneg (le_min (total_nonneg H _ Y) hR.le)]
      exact min_le_right _ _
  have hpoint : ∀ᵐ Y ∂gaussianProduct,
      Tendsto (fun j => min (total H (k (s j)) Y) R) atTop (𝓝 R) := by
    filter_upwards [he] with Y hY
    apply tendsto_const_nhds.congr'
    filter_upwards [hY.eventually (eventually_ge_atTop R)] with j hj
    exact (min_eq_right hj).symm
  have ht : Tendsto (fun j => ∫ Y, min (total H (k (s j)) Y) R ∂gaussianProduct) atTop (𝓝 R) := by
    simpa using tendsto_integral_of_dominated_convergence (fun _ => R) hmeas (integrable_const R) hdom hpoint
  have hb (j : ℕ) : (∫ Y, min (total H (k (s j)) Y) R ∂gaussianProduct) ≤ C+(H:ℝ) := by
    have hmin : Integrable (fun Y => min (total H (k (s j)) Y) R) gaussianProduct :=
      (integrable_const R).mono' (hmeas j) (hdom j)
    have hi := integral_mono hmin
      (total_integrable H _) (fun Y => min_le_left (total H (k (s j)) Y) R)
    rw [total_mean] at hi
    exact hi.trans (by linarith [hkb (s j)])
  have hle := le_of_tendsto ht (Eventually.of_forall hb)
  dsimp [R] at hle
  linarith [le_max_left (C+(H:ℝ)) 0]

/-! Source-energy growth is unconditional; projected escape still requires a
clock-variance bound. These corollaries expose that remaining obligation. -/
theorem uniform_native_escape (H : ℝ≥0) (hH : 0 < H) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ᶠ N : ℕ in atTop,
      ‖IBMCenteredRawGrid.centeredClock (H/(N+1)) (N+1)‖^2 ≤
        C*‖sourceGrid (H/(N+1)) (N+1)‖^2) :
    Tendsto (fun N : ℕ => ‖IBMJointIntrinsicDerivative.jointDivergence
      (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))‖) atTop atTop :=
  IBMProjectedGridEscapeCriterion.native_norm_escape _ _ hC
    (source_energy_tendsto_atTop H hH) hv

theorem uniform_bounded_clock_escape (H : ℝ≥0) (hH : 0 < H) {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ᶠ N : ℕ in atTop,
      ‖IBMCenteredRawGrid.centeredClock (H/(N+1)) (N+1)‖^2 ≤ C) :
    Tendsto (fun N : ℕ => ‖IBMJointIntrinsicDerivative.jointDivergence
      (IBMRawGridCompensation.gridInput (H/(N+1)) (N+1))‖) atTop atTop :=
  IBMProjectedGridEscapeCriterion.bounded_clock_implies_escape _ _ hC
    (source_energy_tendsto_atTop H hH) hv

end OperatorDerivativeRewrite.Foundation.IBMSourceEnergyGrowth
