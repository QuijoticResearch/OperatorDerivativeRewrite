import Foundation.CubeSchurIntegral

/-! A fixed Euclidean L2 domain for the expanding boundary-chart kernels.
This does not yet identify the chart compression with the full Haar operator. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.CubeBoundaryKernelL2
open QuaternionSU2Representation SU2GaussianConeCoordinates SU2HemisphereChart
open CubeChartAction CubeWilsonSlab CubeAxialSlice FourCubeHemisphereCoercivity
attribute [local irreducible] CubeWilsonSlab.kernel

def mass (X : Boundary) : ℝ := ∑ i, (chartRate (X i)-1)
def cutoff (t : ℝ) : Set Boundary := {X | ∀ i, chartRate (t • X i) ≤ 2}
def envelope (p : Boundary × Boundary) : ℝ :=
  CubeMatchedGround.temporalConstant^7*Real.exp (-mass p.1/32)*Real.exp (-mass p.2/32)
def localKernel (t : ℝ) (p : Boundary × Boundary) : ℝ :=
  (cutoff t ×ˢ cutoff t).indicator
    (fun p => kernel (1/t^2) (boundaryRay p.1 t) (boundaryRay p.2 t)/t^21) p
def limitKernel (p : Boundary × Boundary) : ℝ :=
  ((chartDensity 0)^7*CubeSchurIntegral.temporalConstant)*
    (∫ c : SU2, Real.exp (-CubeRootSchur.effective p.1 p.2 c) ∂law)

theorem mass_nonnegative (X : Boundary) : 0 ≤ mass X :=
  Finset.sum_nonneg (fun i _ => sub_nonneg.mpr (chartRate_ge_one (X i)))

theorem scaled_spatial_lower (t : ℝ) (ht : t ≠ 0) (X : Boundary) (hX : X ∈ cutoff t) :
    mass X/16 ≤ (1/t^2)*spatialAction (boundaryRay X t) := by
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    local_defect_lower (t • X i) (hX i))
  have he : t^2*mass X/4 ≤ chordEnergy (chords X t) := by
    simpa only [chordEnergy,chords,mass,chartRate_smul,← Finset.sum_div,← Finset.mul_sum] using hl
  have hs := axial_coercive (chords X t)
  have hh : t^2*mass X/16 ≤ spatialAction (boundaryRay X t) := by
    change t^2*mass X/16 ≤ spatialAction (axialState (chords X t))
    linarith
  have h := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1/t^2)
  have hc : (1/t^2)*(t^2*mass X/16)=mass X/16 := by field_simp [ht]
  rwa [hc] at h

theorem kernel_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (X Y : Boundary)
    (hX : X ∈ cutoff t) (hY : Y ∈ cutoff t) :
    kernel (1/t^2) (boundaryRay X t) (boundaryRay Y t)/t^21 ≤ envelope (X,Y) := by
  have hb (Z : Boundary) (hZ : Z ∈ cutoff t) :
      Real.exp (-(1/t^2)*spatialAction (boundaryRay Z t)/2) ≤ Real.exp (-mass Z/32) := by
    apply Real.exp_le_exp.mpr
    linarith [scaled_spatial_lower t ht.ne' Z hZ]
  apply (div_le_iff₀ (pow_pos ht 21)).mpr
  have h := CubeMatchedGround.kernel_upper t ht h1 (boundaryRay X t) (boundaryRay Y t)
  apply h.trans
  unfold envelope
  have hm := mul_le_mul (hb X hX) (hb Y hY) (Real.exp_pos _).le (Real.exp_pos _).le
  have hh := mul_le_mul_of_nonneg_right hm
    (mul_nonneg (pow_nonneg CubeMatchedGround.temporalConstant_pos.le 7) (pow_pos ht 21).le)
  convert hh using 1 <;> ring

theorem cutoff_measurable (t : ℝ) : MeasurableSet (cutoff t) := by
  have hc (i : Fin 5) : Continuous (fun X : Boundary => chartRate (t • X i)) := by
    unfold chartRate
    fun_prop
  simpa only [cutoff,Set.ofPred_forall] using
    MeasurableSet.iInter (fun i => measurableSet_le (hc i).measurable measurable_const)

theorem eventually_cutoff (X : Boundary) : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), X ∈ cutoff t := by
  have hi (i : Fin 5) : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), chartRate (t • X i) ≤ 2 := by
    have hc : Continuous (fun t : ℝ => chartRate (t • X i)) := by
      unfold chartRate
      fun_prop
    have hz : chartRate ((0 : ℝ) • X i) < 2 := by norm_num [chartRate]
    filter_upwards [(hc.tendsto 0).eventually (eventually_lt_nhds hz)] with t ht
    exact ht.le
  exact eventually_all.mpr hi

private theorem boundary_measurable (t : ℝ) : Measurable (fun X : Boundary => boundaryRay X t) := by
  apply measurable_pi_iff.mpr
  intro e
  unfold boundaryRay CubeAxialSlice.axialState chords
  cases h : CubeAxialSlice.chordLabel e with
  | none => simp only [Option.elim_none]; exact measurable_const
  | some i =>
    simp only [Option.elim_some]
    exact chart_measurable.comp ((measurable_pi_apply i).const_smul t)

theorem localKernel_measurable (t : ℝ) : Measurable (localKernel t) := by
  exact (((kernel_joint_measurable (1/t^2)).comp
    (((boundary_measurable t).comp measurable_fst).prodMk
      ((boundary_measurable t).comp measurable_snd))).div_const (t^21)).indicator
        ((cutoff_measurable t).prod (cutoff_measurable t))

theorem localKernel_nonnegative (t : ℝ) (ht : 0 < t) (p : Boundary × Boundary) :
    0 ≤ localKernel t p := by
  apply Set.indicator_nonneg
  intro p _
  exact div_nonneg (kernel_positive _ _ _).le (pow_pos ht 21).le

theorem localKernel_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (p : Boundary × Boundary) :
    localKernel t p ≤ envelope p := by
  classical
  unfold localKernel
  by_cases hp : p ∈ cutoff t ×ˢ cutoff t
  · rw [Set.indicator_of_mem hp]
    exact kernel_bound t ht h1 p.1 p.2 hp.1 hp.2
  · rw [Set.indicator_of_notMem hp]
    unfold envelope
    exact mul_nonneg (mul_nonneg (pow_nonneg CubeMatchedGround.temporalConstant_pos.le 7)
      (Real.exp_pos _).le) (Real.exp_pos _).le

theorem localKernel_tendsto (p : Boundary × Boundary) :
    Tendsto (fun t : ℝ => localKernel t p) (𝓝[>] (0 : ℝ)) (𝓝 (limitKernel p)) := by
  apply (CubeSchurIntegral.kernel_tendsto p.1 p.2).congr'
  filter_upwards [(eventually_cutoff p.1).filter_mono nhdsWithin_le_nhds,
    (eventually_cutoff p.2).filter_mono nhdsWithin_le_nhds] with t hX hY
  exact (Set.indicator_of_mem (show p ∈ cutoff t ×ˢ cutoff t from ⟨hX,hY⟩)
    (fun q : Boundary × Boundary =>
      kernel (1/t^2) (boundaryRay q.1 t) (boundaryRay q.2 t)/t^21)).symm

theorem limitKernel_aestronglyMeasurable : AEStronglyMeasurable limitKernel :=
  aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
    (fun t => (localKernel_measurable t).aestronglyMeasurable)
    (ae_of_all _ localKernel_tendsto)

theorem limitKernel_nonnegative (p : Boundary × Boundary) : 0 ≤ limitKernel p := by
  apply ge_of_tendsto (localKernel_tendsto p)
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact localKernel_nonnegative t ht p

theorem limitKernel_bound (p : Boundary × Boundary) : limitKernel p ≤ envelope p := by
  apply le_of_tendsto (localKernel_tendsto p)
  filter_upwards [self_mem_nhdsWithin, (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono
    nhdsWithin_le_nhds] with t ht h1
  exact localKernel_bound t ht h1 p

theorem gaussian_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun X : Boundary => Real.exp (-a*mass X)) := by
  have hi := SU2HaarLaplaceUpper.gaussian_integrable (4*a) (by positivity)
  rw [show (fun X : Boundary => Real.exp (-a*mass X))=
      (fun X => ∏ i : Fin 5, Real.exp (-(4*a)*(chartRate (X i)-1)/4)) by
    funext X
    rw [← Real.exp_sum]
    congr 1
    simp only [mass,← Finset.mul_sum,← Finset.sum_div]
    ring,volume_pi]
  exact Integrable.fintype_prod (fun _ : Fin 5 => hi)

theorem envelope_sq_integrable : Integrable (fun p : Boundary × Boundary => (envelope p)^2) := by
  have hg := gaussian_integrable (1/16) (by norm_num)
  have hi := (hg.mul_prod hg).const_mul ((CubeMatchedGround.temporalConstant^7)^2)
  convert hi using 1
  funext p
  have hx (X : Boundary) : (Real.exp (-mass X/32))^2=Real.exp (-(1/16 : ℝ)*mass X) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  unfold envelope
  rw [mul_pow,mul_pow,hx,hx]
  ring

theorem localKernel_memLp (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) :
    MemLp (localKernel t) 2 volume := by
  apply (memLp_two_iff_integrable_sq (localKernel_measurable t).aestronglyMeasurable).mpr
  apply envelope_sq_integrable.mono'
    ((localKernel_measurable t).pow_const 2).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (localKernel_nonnegative t ht p) (localKernel_bound t ht h1 p) 2

theorem limitKernel_memLp : MemLp limitKernel 2 volume := by
  apply (memLp_two_iff_integrable_sq limitKernel_aestronglyMeasurable).mpr
  apply envelope_sq_integrable.mono' (limitKernel_aestronglyMeasurable.pow 2)
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (limitKernel_nonnegative p) (limitKernel_bound p) 2

private theorem error_bound (t : ℝ) (ht : 0 < t) (h1 : t ≤ 1) (p : Boundary × Boundary) :
    ‖(localKernel t p-limitKernel p)^2‖ ≤ 4*(envelope p)^2 := by
  have ha := localKernel_nonnegative t ht p
  have hb := limitKernel_nonnegative p
  have hc := localKernel_bound t ht h1 p
  have hd := limitKernel_bound p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  nlinarith [mul_nonneg ha hb, pow_le_pow_left₀ ha hc 2, pow_le_pow_left₀ hb hd 2]

/-- Genuine squared-L2 convergence on the fixed thirty-dimensional Euclidean domain.
The kernels include both expanding boundary cutoffs and the complete temporal Haar integral. -/
theorem integral_sq_error_tendsto :
    Tendsto (fun t : ℝ => ∫ p : Boundary × Boundary, (localKernel t p-limitKernel p)^2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h : Tendsto
      (fun t : ℝ => ∫ p : Boundary × Boundary, (localKernel t p-limitKernel p)^2)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ _ : Boundary × Boundary, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (fun p : Boundary × Boundary => 4*(envelope p)^2)
    · exact Eventually.of_forall (fun t =>
        (((localKernel_measurable t).aestronglyMeasurable.sub
          limitKernel_aestronglyMeasurable).pow 2))
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_le_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht h1
      exact ae_of_all _ (error_bound t ht h1)
    · exact envelope_sq_integrable.const_mul 4
    · exact ae_of_all _ (fun p => by
        have hp := ((localKernel_tendsto p).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => limitKernel p) (𝓝[>] (0:ℝ))
            (𝓝 (limitKernel p)))).pow 2
        simpa only [sub_self,zero_pow (by norm_num : (2:ℕ)≠0)] using hp)
  simpa only [integral_zero] using h

end OperatorDerivativeRewrite.Foundation.CubeBoundaryKernelL2
