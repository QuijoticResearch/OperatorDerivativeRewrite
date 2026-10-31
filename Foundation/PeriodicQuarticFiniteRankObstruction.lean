import Foundation.PeriodicQuarticCenteredObstruction
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Order.Chebyshev
/-! No uniformly fixed finite-rank operator approximation on actual Wilson
quartic tails along a cofinal large-coupling family. Arbitrarily many dyadic
center-even inverse-ground packets have diagonal form control and small
relative cross-forms. Rank-nullity imposes BOTH stationary mean zero and the
approximation kernel, yielding a nonzero gauge-invariant center-even witness.
The approximation range must explicitly be finite dimensional. Coupling is
chosen after the rank bound and before the approximating operator. This is
not a single noncompact limit operator, a gap-closing rate or a continuum
theorem. All native objects are the verified finite-lattice constructions. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open OperatorDerivativeRewrite.Foundation
namespace OperatorDerivativeRewrite.Foundation.PeriodicQuarticFiniteRankObstruction
open QuaternionSU2Representation SU2JointPlaquetteCubic PeriodicLoopVariation
open PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSlabGround PeriodicSlabL2
open PeriodicQuarticNativeObstruction PeriodicQuarticCenterEven PeriodicQuarticCenteredObstruction
attribute [local irreducible] kernel temporalAction boundaryHaar pairing

def amplitude (j : ℕ) (t : ℝ) : ℝ := (2 : ℝ)^j*t

theorem amplitude_succ (j : ℕ) (t : ℝ) : amplitude (j+1) t=2*amplitude j t := by
  unfold amplitude
  rw [pow_succ]
  ring

theorem amplitude_pos (j : ℕ) (t : ℝ) (ht : 0<t) : 0<amplitude j t := mul_pos (by positivity) ht

theorem amplitude_base (j : ℕ) (t : ℝ) (ht : 0≤t) : t≤amplitude j t := by
  have h : (1 : ℝ)≤2^j := one_le_pow₀ (by norm_num)
  simpa only [one_mul,amplitude] using mul_le_mul_of_nonneg_right h ht

theorem amplitude_mono (i j : ℕ) (hij : i≤j) (t : ℝ) (ht : 0≤t) : amplitude i t≤amplitude j t := by
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ)≤2) hij) ht

theorem gap_of_steps (D : ℕ → ℝ) (n : ℕ) (d : ℝ) (hd : 0≤d)
    (hstep : ∀ k<n,d≤D (k+1)-D k) (i j : ℕ) (hij : i<j) (hj : j≤n) : d≤D j-D i := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
    have hs := hstep j (by omega)
    by_cases he : i=j
    · subst i
      exact hs
    · have hi : i<j := by omega
      have hp := ih i hi (by omega)
      linarith

theorem dyadic_level_gap (n : ℕ) (t : ℝ) (ht : 0<t) (hsmall : amplitude n t≤1/16)
    (i j : ℕ) (hij : i<j) (hj : j≤n) :
    2*t≤centralDistance (axis 0 (4*amplitude j t))-centralDistance (axis 0 (4*amplitude i t)) := by
  let D := fun k => centralDistance (axis 0 (4*amplitude k t))
  apply gap_of_steps D n (2*t) (by linarith) _ i j hij hj
  intro k hk
  have hp := amplitude_pos k t ht
  have hb := (amplitude_mono k n (by omega) t ht.le).trans hsmall
  have hs := small_angle_gap (amplitude k t) hp hb
  have hbase := amplitude_base k t ht.le
  dsimp [D]
  rw [amplitude_succ]
  rw [show (4*(2*amplitude k t) : ℝ)=8*amplitude k t by ring]
  linarith

theorem dyadic_band_gap (n : ℕ) (t r : ℝ) (ht : 0<t) (hsmall : amplitude n t≤1/16)
    (hr : 8*r≤t) (i j : ℕ) (hij : i<j) (hj : j≤n)
    (U V : State) (hU : InBand (amplitude i t) r U) (hV : InBand (amplitude j t) r V) :
    t≤level V-level U := by
  have hg := dyadic_level_gap n t ht hsmall i j hij hj
  exact by linarith [hU.2,hV.1]

theorem dyadic_kernel_upper {β : ℝ} (g : GroundData β) (n : ℕ) (t r : ℝ)
    (hb : 0≤β) (ht : 0<t) (hsmall : amplitude n t≤1/16) (hr : 8*r≤t)
    (i j : ℕ) (hij : i<j) (hj : j≤n) (U V : State)
    (hU : centerTrial g (amplitude i t) r U≠0) (hV : centerTrial g (amplitude j t) r V≠0) :
    kernel β U V≤Real.exp (-β*t^2/32) :=
  kernel_level_upper β t hb ht.le U V (dyadic_band_gap n t r ht hsmall hr i j hij hj U V
    (centerTrial_band g _ _ U hU) (centerTrial_band g _ _ V hV))

theorem dyadic_disjoint {β : ℝ} (g : GroundData β) (n : ℕ) (t r : ℝ)
    (ht : 0<t) (hsmall : amplitude n t≤1/16) (hr : 8*r≤t)
    (i j : ℕ) (hi : i≤n) (hj : j≤n) (hij : i≠j) (U : State) :
    centerTrial g (amplitude i t) r U*centerTrial g (amplitude j t) r U=0 := by
  by_cases h0 : centerTrial g (amplitude i t) r U=0
  · rw [h0,zero_mul]
  by_cases h1 : centerTrial g (amplitude j t) r U=0
  · rw [h1,mul_zero]
  have hA := centerTrial_band g _ _ U h0
  have hB := centerTrial_band g _ _ U h1
  have he : i < j ∨ j < i := lt_or_gt_of_ne hij
  rcases he with he|he
  · have h := dyadic_band_gap n t r ht hsmall hr i j he hj U U hA hB
    linarith
  · have h := dyadic_band_gap n t r ht hsmall hr j i he hi U U hB hA
    linarith


variable {β : ℝ} (g : GroundData β)
private instance stationary_probability : IsProbabilityMeasure g.stationary := g.stationary_probability

theorem center_cross_nonneg (s t r : ℝ) :
    0≤ inner ℝ (operator g (nativeCenter g t r)) (nativeCenter g s r) := by
  have hp : 0≤pairing β (weightTrial g s r) (weightTrial g t r) := by
    unfold pairing
    apply MeasureTheory.integral_nonneg
    intro U
    apply mul_nonneg (weightTrial_bounds g s r U).1
    apply MeasureTheory.integral_nonneg
    intro V
    exact mul_nonneg (kernel_positive β U V).le (weightTrial_bounds g t r V).1
  unfold nativeCenter
  rw [native_cross g _ _ (centerTrial_measurable g s r) (centerTrial_measurable g t r)
    _ _ (centerTrial_bound g s r) (centerTrial_bound g t r)]
  exact div_nonneg hp (mul_pos g.value_pos g.normalizer_pos).le

theorem dyadic_cross_upper (n : ℕ) (t r : ℝ) (hb : 0≤β) (ht : 0<t)
    (hsmall : amplitude n t≤1/16) (hr : 8*r≤t) (i j : ℕ) (hij : i<j) (hj : j≤n) :
    inner ℝ (operator g (nativeCenter g (amplitude j t) r)) (nativeCenter g (amplitude i t) r)≤
      Real.exp (-β*t^2/32)/(g.value*g.normalizer) := by
  unfold nativeCenter
  rw [native_cross g _ _ (centerTrial_measurable g _ r) (centerTrial_measurable g _ r)
    _ _ (centerTrial_bound g _ r) (centerTrial_bound g _ r)]
  apply div_le_div_of_nonneg_right _ (mul_pos g.value_pos g.normalizer_pos).le
  apply pairing_unit_bound β _ _ (weightTrial_measurable g _ r) (weightTrial_measurable g _ r)
    (weightTrial_bounds g _ r) (weightTrial_bounds g _ r) _ (Real.exp_pos _).le
  intro U hU V hV
  have hu : centerTrial g (amplitude i t) r U≠0 := fun h => hU (by simp [weightTrial,h])
  have hv : centerTrial g (amplitude j t) r V≠0 := fun h => hV (by simp [weightTrial,h])
  exact dyadic_kernel_upper g n t r hb ht hsmall hr i j hij hj U V hu hv

theorem relative_from_upper (s u t r : ℝ) (hb : 16777216≤β) (hr : 0<r) (h1 : r≤1/8)
    (hheat : β*r^2=1)
    (hraw : inner ℝ (operator g (nativeCenter g u r)) (nativeCenter g s r)≤
      Real.exp (-β*t^2/32)/(g.value*g.normalizer)) :
    inner ℝ (operator g (nativeCenter g u r)) (nativeCenter g s r)≤
      crossCoefficient β t*(‖nativeCenter g s r‖*‖nativeCenter g u r‖) := by
  have hbpos : 0<β := by linarith
  let D := relativeLower^192/(64*g.normalizer*β^288)
  have h0 := center_norm_floor g s r hr h1
  have h2 := center_norm_floor g u r hr h1
  rw [beta_radius_power β r hheat] at h0 h2
  have he : relativeLower^192*(1/β^288)/(64*g.normalizer)=D := by dsimp [D]; ring
  rw [he] at h0 h2
  have hprod : D≤‖nativeCenter g s r‖*‖nativeCenter g u r‖ := by
    by_cases hn : ‖nativeCenter g s r‖≤‖nativeCenter g u r‖
    · exact h0.trans (by nlinarith [mul_le_mul_of_nonneg_left hn (norm_nonneg (nativeCenter g s r))])
    · exact h2.trans (by nlinarith [mul_le_mul_of_nonneg_right (le_of_not_ge hn) (norm_nonneg (nativeCenter g u r))])
  have hLam := PeriodicGaugeSaturatedGround.eigenvalue_matching_lower β hb g
  have hden := mul_le_mul_of_nonneg_right hLam g.normalizer_pos.le
  have hdenpos : 0<(PeriodicGaugeSaturatedGround.eigenLowerConstant/β^288)*g.normalizer :=
    mul_pos (div_pos PeriodicGaugeSaturatedGround.eigenLowerConstant_pos (pow_pos hbpos _)) g.normalizer_pos
  have hdiv := div_le_div_of_nonneg_left (Real.exp_pos (-β*t^2/32)).le hdenpos hden
  have hid : Real.exp (-β*t^2/32)/((PeriodicGaugeSaturatedGround.eigenLowerConstant/β^288)*g.normalizer)=crossCoefficient β t*D := by
    unfold crossCoefficient
    dsimp [D]
    field_simp [hbpos.ne',g.normalizer_pos.ne',relativeLower_pos.ne',PeriodicGaugeSaturatedGround.eigenLowerConstant_pos.ne']
    <;> ring
  exact hraw.trans (hdiv.trans (hid.le.trans
    (mul_le_mul_of_nonneg_left hprod (crossCoefficient_nonneg β t))))

def packetVector (m : ℕ) (t r : ℝ) (i : Fin m) : StateL2 g := nativeCenter g (amplitude i.val t) r

theorem packetVector_orthogonal (m : ℕ) (t r : ℝ) (ht : 0<t)
    (hsmall : amplitude m t≤1/16) (hr : 8*r≤t) (i j : Fin m) (hij : i≠j) :
    inner ℝ (packetVector g m t r i) (packetVector g m t r j)=0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ _ : State,(0 : ℝ) ∂g.stationary := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (centerTrial_memLp g (amplitude i.val t) r),
        MemLp.coeFn_toLp (centerTrial_memLp g (amplitude j.val t) r)] with U h0 h1
      change packetVector g m t r i U=centerTrial g (amplitude i.val t) r U at h0
      change packetVector g m t r j U=centerTrial g (amplitude j.val t) r U at h1
      rw [h0,h1]
      change centerTrial g (amplitude j.val t) r U*centerTrial g (amplitude i.val t) r U=0
      rw [mul_comm]
      exact dyadic_disjoint g m t r ht hsmall hr i.val j.val i.isLt.le j.isLt.le
        (fun h => hij (Fin.ext h)) U
    _ = 0 := integral_zero _ _

theorem packetVector_cross_abs (m : ℕ) (t r : ℝ) (hb : 16777216≤β) (ht : 0<t)
    (hsmall : amplitude m t≤1/16) (hr : 0<r) (h1 : r≤1/8) (h8 : 8*r≤t)
    (hheat : β*r^2=1) (i j : Fin m) (hij : i≠j) :
    |inner ℝ (operator g (packetVector g m t r j)) (packetVector g m t r i)|≤
      crossCoefficient β t*(‖packetVector g m t r i‖*‖packetVector g m t r j‖) := by
  have hnn : 0≤ inner ℝ (operator g (packetVector g m t r j)) (packetVector g m t r i) := center_cross_nonneg g _ _ r
  rw [abs_of_nonneg hnn]
  have hbpos : 0≤β := by linarith
  have hne : i.val≠j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with he|he
  · exact relative_from_upper g _ _ t r hb hr h1 hheat
      (dyadic_cross_upper g m t r hbpos ht hsmall h8 i.val j.val he j.isLt.le)
  · have h := relative_from_upper g _ _ t r hb hr h1 hheat
      (dyadic_cross_upper g m t r hbpos ht hsmall h8 j.val i.val he i.isLt.le)
    have hs : inner ℝ (operator g (packetVector g m t r j)) (packetVector g m t r i)=
        inner ℝ (operator g (packetVector g m t r i)) (packetVector g m t r j) := by
      rw [operator_symmetric,real_inner_comm]
    rw [hs]
    simpa only [packetVector,mul_comm] using h


def synth (m : ℕ) (F : Fin m → StateL2 g) : (Fin m → ℝ) →ₗ[ℝ] StateL2 g where
  toFun a := ∑ i,a i • F i
  map_add' := by intro a b; simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' := by intro c a; simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]

theorem synth_norm (m : ℕ) (F : Fin m → StateL2 g)
    (horth : ∀ i j,i≠j → inner ℝ (F i) (F j)=0) (a : Fin m → ℝ) :
    ‖synth g m F a‖^2=∑ i,a i^2*‖F i‖^2 := by
  have hinner (i j : Fin m) : inner ℝ (F i) (F j)=if i=j then ‖F i‖^2 else 0 := by
    by_cases h : i=j
    · subst j
      simp [real_inner_self_eq_norm_sq]
    · rw [horth i j h,if_neg h]
  change ‖∑ i,a i • F i‖^2=_
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right,hinner]
  simp [mul_ite,ite_mul,mul_comm,pow_two,mul_assoc]

theorem synth_injective (m : ℕ) (F : Fin m → StateL2 g)
    (horth : ∀ i j,i≠j → inner ℝ (F i) (F j)=0) (hn : ∀ i,0<‖F i‖) :
    Function.Injective (synth g m F) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  have hs := synth_norm g m F horth a
  rw [ha,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)] at hs
  funext i
  have hi := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => mul_nonneg (sq_nonneg (a j)) (sq_nonneg ‖F j‖)) (Finset.mem_univ i)
  rw [← hs] at hi
  have hp : a i^2*‖F i‖^2=0 := le_antisymm hi (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have ha0 : a i^2=0 := (mul_eq_zero.mp hp).resolve_right (sq_pos_of_pos (hn i)).ne'
  exact sq_eq_zero_iff.mp ha0

theorem synth_form (m : ℕ) (F : Fin m → StateL2 g) (a : Fin m → ℝ) :
    inner ℝ (operator g (synth g m F a)) (synth g m F a)=
      ∑ i,∑ j,a i*a j*inner ℝ (operator g (F i)) (F j) := by
  change inner ℝ (operator g (∑ i,a i • F i)) (∑ i,a i • F i)=_
  simp only [map_sum,map_smul,sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hs : inner ℝ (operator g (F j)) (F i)=inner ℝ (operator g (F i)) (F j) := by
    rw [operator_symmetric,real_inner_comm]
  rw [hs]
  ring

theorem synth_rayleigh (m : ℕ) (F : Fin m → StateL2 g) (c e : ℝ) (he : 0≤e)
    (horth : ∀ i j,i≠j → inner ℝ (F i) (F j)=0)
    (hdiag : ∀ i,c*‖F i‖^2≤ inner ℝ (operator g (F i)) (F i))
    (hcross : ∀ i j,i≠j → |inner ℝ (operator g (F i)) (F j)|≤e*(‖F i‖*‖F j‖))
    (a : Fin m → ℝ) :
    (c-(m : ℝ)*e)*‖synth g m F a‖^2≤ inner ℝ (operator g (synth g m F a)) (synth g m F a) := by
  let q := fun i : Fin m => |a i| *‖F i‖
  have hq0 (i : Fin m) : 0≤q i := mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hentry (i j : Fin m) :
      (if i=j then c*(a i^2*‖F i‖^2) else 0)-e*(q i*q j)≤
        a i*a j*inner ℝ (operator g (F i)) (F j) := by
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl]
      have hd := mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg (a i))
      have hl := mul_nonneg he (mul_nonneg (hq0 i) (hq0 i))
      nlinarith
    · rw [if_neg hij,zero_sub]
      have hp : |a i*a j*inner ℝ (operator g (F i)) (F j)|≤e*(q i*q j) := by
        calc
          _ = (|a i| *|a j|)*|inner ℝ (operator g (F i)) (F j)| := by rw [abs_mul,abs_mul]
          _ ≤ (|a i| *|a j|)*(e*(‖F i‖*‖F j‖)) :=
            mul_le_mul_of_nonneg_left (hcross i j hij) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = _ := by dsimp [q]; ring
      exact neg_le_of_abs_le hp
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hentry i j))
  simp only [Finset.sum_sub_distrib] at hsum
  have hd : (∑ i : Fin m,∑ j : Fin m,if i=j then c*(a i^2*‖F i‖^2) else 0)=
      c*(∑ i,a i^2*‖F i‖^2) := by simp [← Finset.mul_sum]
  have hl : (∑ i : Fin m,∑ j : Fin m,e*(q i*q j))=e*(∑ i,q i)^2 := by
    simp only [← mul_assoc,← Finset.mul_sum,← Finset.sum_mul]
    ring
  rw [hd,hl,← synth_form] at hsum
  have hq : (∑ i : Fin m,(q i)^2)=∑ i,a i^2*‖F i‖^2 := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp [q]
    rw [mul_pow,sq_abs]
  have hCS := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := q)
  simp only [Finset.card_univ,Fintype.card_fin] at hCS
  rw [hq] at hCS
  have heCS := mul_le_mul_of_nonneg_left hCS he
  rw [synth_norm g m F horth a]
  nlinarith



def moment (m : ℕ) (w : Fin m → ℝ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun a := ∑ i,a i*w i
  map_add' := by intro a b; simp only [Pi.add_apply,add_mul,Finset.sum_add_distrib]
  map_smul' := by intro c a; simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply,Finset.mul_sum,mul_assoc]

theorem coefficient_kernel (N : ℕ) (F : Fin (N+2) → StateL2 g) (w : Fin (N+2) → ℝ)
    (Q : StateL2 g →L[ℝ] StateL2 g) [FiniteDimensional ℝ Q.toLinearMap.range]
    (hQ : Module.finrank ℝ Q.toLinearMap.range≤N) :
    ∃ a : Fin (N+2) → ℝ,a≠0 ∧ (∑ i,a i*w i)=0 ∧ Q (synth g (N+2) F a)=0 := by
  let T : (Fin (N+2) → ℝ) →ₗ[ℝ] ℝ × Q.toLinearMap.range :=
    (moment (N+2) w).prod (Q.toLinearMap.rangeRestrict.comp (synth g (N+2) F))
  have hd : Module.finrank ℝ (ℝ × Q.toLinearMap.range)<Module.finrank ℝ (Fin (N+2) → ℝ) := by
    simp only [Module.finrank_prod,Module.finrank_self,Module.finrank_pi,Fintype.card_fin]
    omega
  have hk := LinearMap.ker_ne_bot_of_finrank_lt (f := T) hd
  obtain ⟨a,ha,hane⟩ := (LinearMap.ker T).ne_bot_iff.mp hk
  change T a=0 at ha
  have hm := congrArg Prod.fst ha
  change (∑ i,a i*w i)=0 at hm
  have hz := congrArg (fun p : ℝ × Q.toLinearMap.range => (p.2 : StateL2 g)) ha
  change Q (synth g (N+2) F a)=0 at hz
  exact ⟨a,hane,hm,hz⟩

theorem synth_repr (m : ℕ) (F : Fin m → StateL2 g) (a : Fin m → ℝ) :
    ∀ᵐ U ∂g.stationary,synth g m F a U=∑ i,a i*F i U := by
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin m => a i • F i)
  have hm : ∀ᵐ U ∂g.stationary,∀ i : Fin m,(a i • F i) U=a i*F i U :=
    Filter.eventually_all.mpr (fun i => by
      filter_upwards [Lp.coeFn_smul (a i) (F i)] with U hU
      exact hU)
  filter_upwards [hs,hm] with U hsum hscalar
  change synth g m F a U=∑ i,(a i • F i) U at hsum
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact hscalar i

theorem synth_mean (m : ℕ) (F : Fin m → StateL2 g) (a : Fin m → ℝ) :
    (∫ U,synth g m F a U ∂g.stationary)=∑ i,a i*(∫ U,F i U ∂g.stationary) := by
  rw [integral_congr_ae (synth_repr g m F a),integral_finsetSum Finset.univ
    (fun i _ => ((Lp.memLp (F i)).integrable (by norm_num)).const_mul (a i))]
  simp_rw [integral_const_mul]

def synthRaw (m : ℕ) (t r : ℝ) (a : Fin m → ℝ) (U : State) : ℝ :=
  ∑ i,a i*centerTrial g (amplitude i.val t) r U

theorem synth_packet_repr (m : ℕ) (t r : ℝ) (a : Fin m → ℝ) :
    ∀ᵐ U ∂g.stationary,synth g m (packetVector g m t r) a U=synthRaw g m t r a U := by
  have hm : ∀ᵐ U ∂g.stationary,∀ i : Fin m,packetVector g m t r i U=centerTrial g (amplitude i.val t) r U :=
    Filter.eventually_all.mpr (fun i => MemLp.coeFn_toLp (centerTrial_memLp g (amplitude i.val t) r))
  filter_upwards [synth_repr g m (packetVector g m t r) a,hm] with U hsum hpoint
  rw [hsum]
  unfold synthRaw
  apply Finset.sum_congr rfl
  intro i _
  rw [hpoint i]

theorem synthRaw_even (m : ℕ) (t r : ℝ) (a : Fin m → ℝ) (j : Fin 3) (U : State) :
    synthRaw g m t r a (PeriodicCenterSeam.flip j U)=synthRaw g m t r a U := by
  unfold synthRaw
  simp_rw [centerTrial_even]

theorem synthRaw_invariant (m : ℕ) (t r : ℝ) (a : Fin m → ℝ) (b : Gauge) (U : State) :
    synthRaw g m t r a (PeriodicSlabGauge.gaugeAction b U)=synthRaw g m t r a U := by
  unfold synthRaw
  simp_rw [centerTrial_invariant]

theorem synth_packet_even (m : ℕ) (t r : ℝ) (a : Fin m → ℝ) (j : Fin 3) :
    ∀ᵐ U ∂g.stationary,synth g m (packetVector g m t r) a (PeriodicCenterSeam.flip j U)=
      synth g m (packetVector g m t r) a U := by
  have hf := synth_packet_repr g m t r a
  have hi := (PeriodicGroundSeamParity.stationary_preserving g j).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [hf,hi] with U h0 h1
  change synth g m (packetVector g m t r) a (PeriodicCenterSeam.flip j U)=synthRaw g m t r a (PeriodicCenterSeam.flip j U) at h1
  rw [h0,h1,synthRaw_even]

theorem synth_packet_avoids (m : ℕ) (t r M : ℝ) (a : Fin m → ℝ)
    (ha : ∀ i : Fin m,AvoidsFlat β M (centerTrial g (amplitude i.val t) r)) :
    ∀ᵐ U ∂g.stationary,∀ V : State,spatialAction V=0 → ∀ b : Gauge,
      β*temporalAction U V b<M → synth g m (packetVector g m t r) a U=0 := by
  filter_upwards [synth_packet_repr g m t r a] with U hU
  intro V hV b hclose
  rw [hU]
  have hz (i : Fin m) : centerTrial g (amplitude i.val t) r U=0 := ha i U V hV b hclose
  unfold synthRaw
  simp only [hz,mul_zero,Finset.sum_const_zero]



open Filter
open scoped Topology

theorem eventual_single_packet (j : ℕ) : ∀ᶠ x : ℝ in 𝓝[>] 0,∀ q : GroundData (1/x^6),
    0<‖nativeCenter q (amplitude j (x^2)) (x^3)‖ ∧
      (nativeConstant/8)*‖nativeCenter q (amplitude j (x^2)) (x^3)‖^2≤ inner ℝ
        (operator q (nativeCenter q (amplitude j (x^2)) (x^3))) (nativeCenter q (amplitude j (x^2)) (x^3)) ∧
      AvoidsFlat (1/x^6) (1/(256*x^2)) (centerTrial q (amplitude j (x^2)) (x^3)) := by
  have hxpow : Tendsto (fun x : ℝ => x^2) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 2
  have htend : Tendsto (fun x : ℝ => amplitude j (x^2)) (𝓝 0) (𝓝 0) := by
    simpa only [amplitude,mul_zero] using hxpow.const_mul ((2 : ℝ)^j)
  have hpotend : Tendsto (fun x : ℝ => ((2 : ℝ)^j)^4*x^2) (𝓝 0) (𝓝 0) := by
    simpa only [mul_zero] using hxpow.const_mul (((2 : ℝ)^j)^4)
  have hsin := htend.eventually eventual_sine_conditions
  have hpot := hpotend.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1))
  have hsmall : ∀ᶠ x : ℝ in 𝓝 0,x<(1/256 : ℝ) := Iio_mem_nhds (by norm_num)
  filter_upwards [hsin.filter_mono nhdsWithin_le_nhds,hpot.filter_mono nhdsWithin_le_nhds,
    hsmall.filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] 0,0<x)] with x hsin hpot hxsmall hx q
  change 0<x at hx
  have hr : 0<x^3 := pow_pos hx 3
  have hr1 : x^3≤1/8 := by
    have h := pow_le_pow_left₀ hx.le hxsmall.le 3
    norm_num at h
    linarith
  have ht := amplitude_pos j (x^2) (pow_pos hx 2)
  have hbase := amplitude_base j (x^2) (sq_nonneg x)
  have hnarrow : 256*x^3≤amplitude j (x^2) := by
    have h := mul_le_mul_of_nonneg_right (show (256 : ℝ)*x≤1 by linarith) (sq_nonneg x)
    nlinarith
  have hb : 0≤1/x^6 := (one_div_pos.mpr (pow_pos hx 6)).le
  have hheat : (1/x^6)*(x^3)^2=1 := by field_simp [hx.ne']
  have hpotential : (1/x^6)*(amplitude j (x^2))^4≤1 := by
    have he : (1/x^6)*(amplitude j (x^2))^4=((2 : ℝ)^j)^4*x^2 := by
      unfold amplitude
      field_simp [hx.ne']
      <;> ring
    rw [he]
    exact hpot.le
  have hn := nativeCenter_norm_pos q (amplitude j (x^2)) (x^3) (nativeTrial_norm_pos q (amplitude j (x^2)) (x^3) hr (by linarith))
  have hf := nativeCenter_lower q _ _ (uniform_native_lower q _ _ hb ht hr hr1 hnarrow
    hsin.1 hsin.2 hheat hpotential)
  have ha := centerTrial_flat_budget q _ _ hb ht.le hr.le hnarrow hsin.2
  have hbudget : 1/(256*x^2)≤(1/x^6)*(amplitude j (x^2))^2/256 := by
    have hs := pow_le_pow_left₀ (sq_nonneg x) hbase 2
    have hm := mul_le_mul_of_nonneg_left hs (div_nonneg hb (by norm_num : (0 : ℝ)≤256))
    have he : ((1/x^6)/256)*(x^2)^2=1/(256*x^2) := by field_simp [hx.ne']
    rw [he] at hm
    convert hm using 1 <;> ring
  exact ⟨hn,hf,avoids_mono _ _ _ ha hbudget⟩

def GoodPackets (m : ℕ) (t r M : ℝ) : Prop :=
  (∀ i : Fin m,0<‖packetVector g m t r i‖) ∧
  (∀ i j : Fin m,i≠j → inner ℝ (packetVector g m t r i) (packetVector g m t r j)=0) ∧
  (∀ i : Fin m,(nativeConstant/8)*‖packetVector g m t r i‖^2≤ inner ℝ
    (operator g (packetVector g m t r i)) (packetVector g m t r i)) ∧
  (∀ i j : Fin m,i≠j → |inner ℝ (operator g (packetVector g m t r j)) (packetVector g m t r i)|≤
    (nativeConstant/(16*(m : ℝ)))*(‖packetVector g m t r i‖*‖packetVector g m t r j‖)) ∧
  (∀ i : Fin m,AvoidsFlat β M (centerTrial g (amplitude i.val t) r))

theorem goodPackets_mono (m : ℕ) (t r A B : ℝ) (hg : GoodPackets g m t r B) (hAB : A≤B) :
    GoodPackets g m t r A :=
  ⟨hg.1,hg.2.1,hg.2.2.1,hg.2.2.2.1,fun i => avoids_mono _ _ _ (hg.2.2.2.2 i) hAB⟩

theorem eventual_good_packets (m : ℕ) (hm : 0<m) :
    ∀ᶠ x : ℝ in 𝓝[>] 0,∀ q : GroundData (1/x^6),GoodPackets q m (x^2) (x^3) (1/(256*x^2)) := by
  have hall : ∀ᶠ x : ℝ in 𝓝[>] 0,∀ i : Fin m,∀ q : GroundData (1/x^6),
      0<‖nativeCenter q (amplitude i.val (x^2)) (x^3)‖ ∧
      (nativeConstant/8)*‖nativeCenter q (amplitude i.val (x^2)) (x^3)‖^2≤ inner ℝ
        (operator q (nativeCenter q (amplitude i.val (x^2)) (x^3))) (nativeCenter q (amplitude i.val (x^2)) (x^3)) ∧
      AvoidsFlat (1/x^6) (1/(256*x^2)) (centerTrial q (amplitude i.val (x^2)) (x^3)) :=
    Filter.eventually_all.mpr (fun i => eventual_single_packet i.val)
  have htend : Tendsto (fun x : ℝ => amplitude m (x^2)) (𝓝 0) (𝓝 0) := by
    simpa [amplitude] using
      ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).pow 2).const_mul ((2 : ℝ)^m)
  have hsmall := htend.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/16))
  have heps : (0 : ℝ)<nativeConstant/(16*(m : ℝ)) :=
    div_pos nativeConstant_pos (mul_pos (by norm_num) (by exact_mod_cast hm))
  have he := crossCoefficient_tendsto.eventually (Iio_mem_nhds heps)
  have hlarge := coupling_diverges.eventually (eventually_ge_atTop (16777216 : ℝ))
  have hxsmall : ∀ᶠ x : ℝ in 𝓝 0,x<(1/256 : ℝ) := Iio_mem_nhds (by norm_num)
  filter_upwards [hall,hsmall.filter_mono nhdsWithin_le_nhds,he,hlarge,
    hxsmall.filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : ∀ᶠ x : ℝ in 𝓝[>] 0,0<x)] with x hall hsmall he hlarge hxsmall hx q
  change 0<x at hx
  have ht : 0<x^2 := pow_pos hx 2
  have hr : 0<x^3 := pow_pos hx 3
  have hr1 : x^3≤1/8 := by
    have h := pow_le_pow_left₀ hx.le hxsmall.le 3
    norm_num at h
    linarith
  have h8 : 8*x^3≤x^2 := by
    have h := mul_le_mul_of_nonneg_right (show (256 : ℝ)*x≤1 by linarith) (sq_nonneg x)
    nlinarith
  have hheat : (1/x^6)*(x^3)^2=1 := by field_simp [hx.ne']
  refine ⟨fun i => (hall i q).1,?_,fun i => (hall i q).2.1,?_,fun i => (hall i q).2.2⟩
  · intro i j hij
    exact packetVector_orthogonal q m _ _ ht hsmall.le h8 i j hij
  · intro i j hij
    have hc := packetVector_cross_abs q m _ _ hlarge ht hsmall.le hr hr1 h8 hheat i j hij
    exact hc.trans (mul_le_mul_of_nonneg_right he.le (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem arbitrarily_large_packets (m : ℕ) (hm : 0<m) (M : ℝ) :
    ∃ β : ℝ,1≤β ∧ M≤β ∧ ∃ q : GroundData β,∃ t r : ℝ,GoodPackets q m t r M := by
  have hb := coupling_diverges.eventually (eventually_ge_atTop (max M 1))
  have he := flat_distance_diverges.eventually (eventually_ge_atTop M)
  obtain ⟨x,hfamily,hbeta,hescape⟩ := ((eventual_good_packets m hm).and (hb.and he)).exists
  let q := ground (1/x^6)
  refine ⟨1/x^6,(le_max_right M 1).trans hbeta,(le_max_left M 1).trans hbeta,q,x^2,x^3,?_⟩
  exact goodPackets_mono q m _ _ _ _ (hfamily q) hescape



theorem packet_rank_witness (N : ℕ) (t r M : ℝ) (hg : GoodPackets g (N+2) t r M)
    (Q : StateL2 g →L[ℝ] StateL2 g) [FiniteDimensional ℝ Q.toLinearMap.range]
    (hQ : Module.finrank ℝ Q.toLinearMap.range≤N) :
    ∃ a : Fin (N+2) → ℝ,0<‖synth g (N+2) (packetVector g (N+2) t r) a‖ ∧
      (∫ U,synth g (N+2) (packetVector g (N+2) t r) a U ∂g.stationary)=0 ∧
      (∀ j : Fin 3,∀ᵐ U ∂g.stationary,synth g (N+2) (packetVector g (N+2) t r) a (PeriodicCenterSeam.flip j U)=
        synth g (N+2) (packetVector g (N+2) t r) a U) ∧
      Q (synth g (N+2) (packetVector g (N+2) t r) a)=0 ∧
      (nativeConstant/16)*‖synth g (N+2) (packetVector g (N+2) t r) a‖^2≤ inner ℝ
        (operator g (synth g (N+2) (packetVector g (N+2) t r) a)) (synth g (N+2) (packetVector g (N+2) t r) a) ∧
      (∀ᵐ U ∂g.stationary,∀ V : State,spatialAction V=0 → ∀ b : Gauge,
        β*temporalAction U V b<M → synth g (N+2) (packetVector g (N+2) t r) a U=0) := by
  let F := packetVector g (N+2) t r
  let w := fun i : Fin (N+2) => ∫ U,F i U ∂g.stationary
  obtain ⟨a,hane,hmean,hkill⟩ := coefficient_kernel g N F w Q hQ
  have hinj := synth_injective g (N+2) F hg.2.1 hg.1
  have hne : synth g (N+2) F a≠0 := by
    intro hz
    apply hane
    apply hinj
    exact hz.trans (map_zero (synth g (N+2) F)).symm
  have hnorm : 0<‖synth g (N+2) F a‖ := norm_pos_iff.mpr hne
  have hm : (∫ U,synth g (N+2) F a U ∂g.stationary)=0 :=
    (synth_mean g (N+2) F a).trans hmean
  have hmpos : (0 : ℝ)<(N+2 : ℕ) := by positivity
  have hep : 0≤nativeConstant/(16*((N+2 : ℕ) : ℝ)) :=
    (div_pos nativeConstant_pos (mul_pos (by norm_num) hmpos)).le
  have hcross (i j : Fin (N+2)) (hij : i≠j) :
      |inner ℝ (operator g (F i)) (F j)|≤(nativeConstant/(16*((N+2 : ℕ) : ℝ)))*(‖F i‖*‖F j‖) := by
    simpa only [mul_comm] using hg.2.2.2.1 j i hij.symm
  have hform := synth_rayleigh g (N+2) F (nativeConstant/8) (nativeConstant/(16*((N+2 : ℕ) : ℝ)))
    hep hg.2.1 hg.2.2.1 hcross a
  have he : nativeConstant/8-((N+2 : ℕ) : ℝ)*(nativeConstant/(16*((N+2 : ℕ) : ℝ)))=nativeConstant/16 := by
    field_simp [hmpos.ne']
    <;> ring
  rw [he] at hform
  exact ⟨a,hnorm,hm,synth_packet_even g (N+2) t r a,hkill,hform,
    synth_packet_avoids g (N+2) t r M a hg.2.2.2.2⟩

theorem rayleigh_error_lower (H : StateL2 g) (hH : 0<‖H‖)
    (hform : (nativeConstant/16)*‖H‖^2≤ inner ℝ (operator g H) H)
    (Q : StateL2 g →L[ℝ] StateL2 g) (hQ : Q H=0) : nativeConstant/16≤‖operator g-Q‖ := by
  have he : (operator g-Q) H=operator g H := by rw [sub_apply,hQ,sub_zero]
  have hc := real_inner_le_norm ((operator g-Q) H) H
  have ho := ContinuousLinearMap.le_opNorm (operator g-Q) H
  rw [he] at hc ho
  have hh := hform.trans (hc.trans (mul_le_mul_of_nonneg_right ho (norm_nonneg _)))
  have h : (nativeConstant/16)*‖H‖^2≤‖operator g-Q‖*‖H‖^2 := by convert hh using 1 <;> ring
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos hH)).mp h

theorem packet_finite_rank_obstruction (N : ℕ) (t r M : ℝ) (hg : GoodPackets g (N+2) t r M)
    (Q : StateL2 g →L[ℝ] StateL2 g) [FiniteDimensional ℝ Q.toLinearMap.range]
    (hQ : Module.finrank ℝ Q.toLinearMap.range≤N) : nativeConstant/16≤‖operator g-Q‖ := by
  obtain ⟨a,hn,_,_,hq,hf,_⟩ := packet_rank_witness g N t r M hg Q hQ
  exact rayleigh_error_lower g _ hn hf Q hq

theorem arbitrarily_large_finite_rank_obstruction (N : ℕ) (M : ℝ) :
    ∃ β : ℝ,1≤β ∧ M≤β ∧ ∃ q : GroundData β,
      ∀ Q : StateL2 q →L[ℝ] StateL2 q,FiniteDimensional ℝ Q.toLinearMap.range →
        Module.finrank ℝ Q.toLinearMap.range≤N → nativeConstant/16≤‖operator q-Q‖ := by
  obtain ⟨β,hb,hM,q,t,r,hg⟩ := arbitrarily_large_packets (N+2) (by omega) M
  refine ⟨β,hb,hM,q,?_⟩
  intro Q hfinite hQ
  letI := hfinite
  exact packet_finite_rank_obstruction q N t r M hg Q hQ


end OperatorDerivativeRewrite.Foundation.PeriodicQuarticFiniteRankObstruction
