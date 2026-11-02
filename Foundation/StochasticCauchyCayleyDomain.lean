import Foundation.StochasticCauchyJointBoundaryObstruction
import Foundation.StochasticCauchyExitLaw
import Mathlib.Analysis.Complex.Conformal
noncomputable section
open MeasureTheory Set Filter AddCircle
open scoped NNReal ENNReal Topology
namespace OperatorDerivativeRewrite.Foundation.StochasticCauchyCayleyDomain
open InfiniteGaussian StochasticCauchyExitOccupation StochasticCauchyExitLaw
private abbrev μ := gaussianProduct.prod gaussianProduct
private abbrev Angle := AddCircle (1:ℝ)

theorem unit_exit_avoid_pole : ∀ᵐ w ∂μ,exitValue 1 w≠1 := by
  have hm : Measurable (fun x : Angle => ((1:ℝ):ℂ)*(AddCircle.toCircle x:ℂ)) := by fun_prop
  have hi : Function.Injective (fun x : Angle => ((1:ℝ):ℂ)*(AddCircle.toCircle x:ℂ)) := by
    intro x y hxy
    apply AddCircle.injective_toCircle (by norm_num : (1:ℝ)≠0)
    apply Subtype.coe_injective
    simpa only [Complex.ofReal_one,one_mul] using hxy
  have hpre : (fun x : Angle => ((1:ℝ):ℂ)*(AddCircle.toCircle x:ℂ)) ⁻¹' {(1:ℂ)}={(0:Angle)} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff]
    have h0 : ((1:ℝ):ℂ)*(AddCircle.toCircle (0:Angle):ℂ)=1 := by simp
    constructor
    · intro hx
      apply hi
      exact hx.trans h0.symm
    · intro hx
      subst x
      exact h0
  have hmap : μ.map (exitValue 1) {(1:ℂ)}=0 := by
    rw [exitValue_law 1 (by norm_num),Measure.map_apply hm (measurableSet_singleton (1:ℂ)),hpre]
    have hv : (volume : Measure Angle)=haarAddCircle := by
      simpa only [ENNReal.ofReal_one,one_smul] using (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ)))
    rw [← hv]
    simpa only [Metric.closedBall_zero,mul_zero,min_eq_right (by norm_num : (0:ℝ)≤1),ENNReal.ofReal_zero] using
      (AddCircle.volume_closedBall (1:ℝ) (x := (0:Angle)) (0:ℝ))
  rw [Measure.map_apply (exitValue_measurable 1) (measurableSet_singleton (1:ℂ))] at hmap
  simpa only [ae_iff,not_not,Set.preimage,Set.mem_singleton_iff] using hmap

/-- Square-summable bilateral Fourier coefficients cannot have a unit jump
between two constant tails. This is the exact range obstruction used below. -/
private theorem no_summable_jump (c : ℤ → ℂ) (hs : Summable (fun n => ‖c n‖^2))
    (hr : ∀ n : ℤ,c n-c (n-1)=if n=0 then 1 else 0) : False := by
  have hp (n : ℕ) : c (n:ℤ)=c 0 := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have h := hr ((n:ℤ)+1)
      rw [if_neg (by omega)] at h
      have heq : c ((n:ℤ)+1)=c (n:ℤ) := by simpa only [add_sub_cancel_right] using sub_eq_zero.mp h
      simpa only [Nat.cast_succ] using heq.trans ih
  have hm (n : ℕ) : c (-(n:ℤ)-1)=c (-1) := by
    induction n with
    | zero => simp only [Nat.cast_zero,neg_zero,zero_sub]
    | succ n ih =>
      have h := hr (-(n:ℤ)-1)
      rw [if_neg (by omega)] at h
      have he : -((n+1:ℕ):ℤ)-1=-(n:ℤ)-1-1 := by omega
      rw [he]
      exact (sub_eq_zero.mp h).symm.trans ih
  have hsp : Summable (fun n : ℕ => ‖c (n:ℤ)‖^2) := hs.comp_injective (by intro n m h;exact_mod_cast h)
  have him : Function.Injective (fun n : ℕ => -(n:ℤ)-1) := by
    intro n m h
    change -(n:ℤ)-1=-(m:ℤ)-1 at h
    have he : (n:ℤ)=(m:ℤ) := by linarith
    exact_mod_cast he
  have hsm : Summable (fun n : ℕ => ‖c (-(n:ℤ)-1)‖^2) := hs.comp_injective him
  have htp := hsp.tendsto_atTop_zero
  have htm := hsm.tendsto_atTop_zero
  simp only [hp] at htp
  simp only [hm] at htm
  have hp0 : c 0=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (tendsto_nhds_unique tendsto_const_nhds htp))
  have hm0 : c (-1)=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp (tendsto_nhds_unique tendsto_const_nhds htm))
  have h := hr 0
  norm_num [hp0,hm0] at h

private theorem fourier_mean (n : ℤ) : (∫ x : Angle,fourier n x ∂haarAddCircle)=if n=0 then 1 else 0 := by
  by_cases hn : n=0
  · subst n
    simp
  · rw [if_neg hn]
    exact integral_eq_zero_of_add_right_eq_neg (μ := haarAddCircle)
      (fourier_add_half_inv_index hn (by norm_num : (0:ℝ)<1))

/-- The constant1 is not in the L2 range of multiplication by1-character.
The proof reuses Mathlib Parseval; no new Fourier/Fejer infrastructure. -/
theorem no_circle_L2_inverse (H : Lp ℂ 2 (haarAddCircle : Measure Angle)) :
    ¬ (∀ᵐ x ∂haarAddCircle,(1-(AddCircle.toCircle x:ℂ))*H x=1) := by
  intro hH
  have hI := (Lp.memLp H).integrable (by norm_num : (1:ℝ≥0∞)≤2)
  have hm (n : ℤ) : Integrable (fun x : Angle => fourier n x*H x) haarAddCircle := by
    simpa only [smul_eq_mul] using hI.fourier_smul n
  have hr (n : ℤ) : fourierCoeff H n-fourierCoeff H (n-1)=if n=0 then 1 else 0 := by
    simp only [fourierCoeff,smul_eq_mul]
    rw [← integral_sub (hm (-n)) (hm (-(n-1)))]
    have he : (fun x : Angle => fourier (-n) x*H x-fourier (-(n-1)) x*H x) =ᵐ[haarAddCircle]
        fun x => fourier (-n) x := by
      filter_upwards [hH] with x hx
      rw [show -(n-1)=(-n)+1 by omega,fourier_add,fourier_one]
      calc
        _ = fourier (-n) x*((1-(AddCircle.toCircle x:ℂ))*H x) := by ring
        _ = _ := by rw [hx,mul_one]
    rw [integral_congr_ae he,fourier_mean]
    simp only [neg_eq_zero]
  exact no_summable_jump (fourierCoeff H) (hasSum_sq_fourierCoeff H).summable hr

/-- The ACTUAL unit-circle exit boundary inverse is not square integrable.
Measurable law transport and Parseval discharge the hypotheses; a divergence
of chosen approximants alone is not used as evidence. -/
theorem boundary_inverse_not_memLp : ¬ MemLp (fun w => (1-exitValue 1 w)⁻¹) 2 μ := by
  intro h
  let f : ℂ → ℂ := fun z => (1-z)⁻¹
  let ψ : Angle → ℂ := fun x => ((1:ℝ):ℂ)*(AddCircle.toCircle x:ℂ)
  have hf : Measurable f := (measurable_const.sub measurable_id).inv
  have hψ : Measurable ψ := by fun_prop
  have hmap : MemLp f 2 (μ.map (exitValue 1)) :=
    (memLp_map_measure_iff hf.aestronglyMeasurable (exitValue_measurable 1).aemeasurable).mpr h
  rw [exitValue_law 1 (by norm_num)] at hmap
  have hcircle : MemLp (f ∘ ψ) 2 haarAddCircle := hmap.comp_of_map hψ.aemeasurable
  let H : Lp ℂ 2 (haarAddCircle : Measure Angle) := hcircle.toLp _
  have hH : H =ᵐ[haarAddCircle] f ∘ ψ := MemLp.coeFn_toLp _
  have hp : ∀ᵐ z ∂μ.map (exitValue 1),z≠1 :=
    (ae_map_iff (exitValue_measurable 1).aemeasurable (measurableSet_singleton (1:ℂ)).compl).mpr unit_exit_avoid_pole
  rw [exitValue_law 1 (by norm_num)] at hp
  have hpCircle := ae_of_ae_map hψ.aemeasurable hp
  apply no_circle_L2_inverse H
  filter_upwards [hH,hpCircle] with x hh hx
  rw [hh]
  simp only [Function.comp_def,f,ψ,Complex.ofReal_one,one_mul] at *
  exact mul_inv_cancel₀ (sub_ne_zero.mpr (Ne.symm hx))

/-- Disk-to-right-half-plane Cayley formula, defined measurably even at its pole. -/
def cayley (z : ℂ) : ℂ := (1+z)/(1-z)

/-- Actual exit trace of the Cayley map lies OUTSIDE the Cauchy operator's L2
domain; source conformal statements require extra integrability hypotheses. -/
theorem cayley_exit_not_memLp : ¬ MemLp (fun w => cayley (exitValue 1 w)) 2 μ := by
  intro h
  apply boundary_inverse_not_memLp
  have hs := (h.add (memLp_const (1:ℂ))).const_smul ((2:ℂ)⁻¹)
  apply hs.ae_eq
  filter_upwards [unit_exit_avoid_pole] with w hw
  change (2:ℂ)⁻¹*(cayley (exitValue 1 w)+1)=(1-exitValue 1 w)⁻¹
  simp only [cayley]
  field_simp [sub_ne_zero.mpr (Ne.symm hw)]
  <;> ring

/-- Exact ordinary complex derivative, with the boundary pole excluded. -/
theorem cayley_hasDerivAt (z : ℂ) (hz : z≠1) : HasDerivAt cayley (2/(1-z)^2) z := by
  have h := ((hasDerivAt_const z (1:ℂ)).add (hasDerivAt_id z)).div
    ((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)) (sub_ne_zero.mpr (Ne.symm hz))
  convert h using 1
  · rfl
  · dsimp
    ring

theorem cayley_conformal (z : ℂ) (hz : ‖z‖<1) : ConformalAt cayley z := by
  have hz1 : z≠1 := by intro h;rw [h,norm_one] at hz;exact (lt_irrefl 1) hz
  have hd := cayley_hasDerivAt z hz1
  apply hd.differentiableAt.conformalAt
  rw [hd.deriv]
  exact div_ne_zero (by norm_num) (pow_ne_zero 2 (sub_ne_zero.mpr (Ne.symm hz1)))

theorem cayley_injective : Set.InjOn cayley {z : ℂ | z≠1} := by
  intro z hz w hw heq
  change (1+z)/(1-z)=(1+w)/(1-w) at heq
  have he := (div_eq_div_iff (sub_ne_zero.mpr (Ne.symm hz)) (sub_ne_zero.mpr (Ne.symm hw))).mp heq
  have h : (2:ℂ)*(z-w)=0 := by linear_combination he
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num))

theorem cayley_re_pos (z : ℂ) (hz : ‖z‖<1) : 0<(cayley z).re := by
  have hz1 : z≠1 := by intro h;rw [h,norm_one] at hz;exact (lt_irrefl 1) hz
  have hd : 0<Complex.normSq (1-z) := Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hn : z.re^2+z.im^2<1 := by
    have h : ‖z‖^2<1 := by nlinarith [norm_nonneg z]
    rw [Complex.sq_norm,Complex.normSq_apply] at h
    nlinarith
  rw [cayley,Complex.div_re]
  simp only [Complex.add_re,Complex.one_re,Complex.sub_re,Complex.add_im,Complex.one_im,
    Complex.sub_im,zero_add,zero_sub]
  rw [← add_div]
  apply div_pos _ hd
  nlinarith

theorem cayley_onto (w : ℂ) (hw : 0<w.re) : ∃ z : ℂ,‖z‖<1 ∧ cayley z=w := by
  have hden : w+1≠0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at he
    linarith
  have hn : ‖w-1‖<‖w+1‖ := by
    have hsq : ‖w-1‖^2<‖w+1‖^2 := by
      simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,
        Complex.add_im,Complex.one_re,Complex.one_im,sub_zero,add_zero]
      nlinarith
    nlinarith [norm_nonneg (w-1),norm_nonneg (w+1)]
  let z : ℂ := (w-1)/(w+1)
  have hz : ‖z‖<1 := by
    dsimp only [z]
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hden)).mpr hn
  have hz1 : z≠1 := by intro h;rw [h,norm_one] at hz;exact (lt_irrefl 1) hz
  refine ⟨z,hz,?_⟩
  dsimp only [cayley,z]
  field_simp [hden,sub_ne_zero.mpr (Ne.symm hz1)]
  <;> ring

/-- The actual conformal example is the disk-to-RIGHT-half-plane map. -/
theorem cayley_image : cayley '' {z : ℂ | ‖z‖<1}={w : ℂ | 0<w.re} := by
  ext w
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact cayley_re_pos z hz
  · intro hw
    obtain ⟨z,hz,hzw⟩ := cayley_onto w hw
    exact ⟨z,hz,hzw⟩

end OperatorDerivativeRewrite.Foundation.StochasticCauchyCayleyDomain
