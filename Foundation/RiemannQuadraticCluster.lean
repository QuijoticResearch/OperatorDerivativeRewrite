import Foundation.RiemannQuadraticZeroTransfer
import Foundation.PureOrderAppellExpansion
import Foundation.PureOrderAppellOrthogonality
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Existing Gaussian Hermite root counts and actual quadratic-flow cluster bounds.
The pure-order Appell bridge transfers monic degree to the exact Hermite family.
Finite simultaneous local branches give an actual m-zero lower count. A joint
parabolic/spatial remainder has a fixed genuine L1 budget even when v/h grows.
Exhaustive cluster confinement and an upper count remain separate obligations. -/
noncomputable section
open Polynomial Set Metric Complex Filter MeasureTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.RiemannQuadraticCluster
open PureOrderAppellCalculus PureOrderAppellExpansion RiemannQuadraticHermite
open RiemannQuadraticZeroTransfer RiemannEvenFlow

theorem appell_recursion (n : ℕ) :
    appell 2 1 (n+2)=X*appell 2 1 (n+1)-C (2*((n : ℝ)+1))*appell 2 1 n := by
  change X*appell 2 1 (n+1)-((2 : ℝ)*1) •
    (derivative^[2-1]) (appell 2 1 (n+1)) = _
  norm_num only [Nat.reduceSub,Function.iterate_one,mul_one]
  rw [appell_derivative,smul_smul]
  simp only [Algebra.smul_def,Polynomial.algebraMap_eq]

def polynomial (n : ℕ) : ℂ[X] := (appell 2 1 n).map (algebraMap ℝ ℂ)

theorem polynomial_recursion (n : ℕ) :
    polynomial (n+2)=X*polynomial (n+1)-C (2*((n : ℂ)+1))*polynomial n := by
  simp [polynomial,appell_recursion]

theorem polynomial_eval (n : ℕ) (w : ℂ) : (polynomial n).eval w=value n w := by
  induction n using Nat.twoStepInduction with
  | zero => simp [polynomial,appell]
  | one => simp [polynomial,appell,raise]
  | more n h0 h1 =>
    rw [polynomial_recursion,eval_sub,eval_mul,eval_X,eval_mul,eval_C,h0,h1,value_recursion]

theorem polynomial_monic (n : ℕ) : (polynomial n).Monic :=
  (appell_monic_degree 2 1 n).monic.map _

theorem polynomial_natDegree (n : ℕ) : (polynomial n).natDegree=n := by
  rw [polynomial,natDegree_map]
  exact (appell_monic_degree 2 1 n).natDegree_eq

theorem polynomial_ne_zero (n : ℕ) : polynomial n ≠ 0 := (polynomial_monic n).ne_zero

theorem derivative_eval_ne_zero_at_root (n : ℕ) (w : ℂ)
    (hw : (polynomial n).eval w=0) : (polynomial n).derivative.eval w ≠ 0 := by
  have hroot : value n w=0 := by simpa only [polynomial_eval] using hw
  have he : (fun w : ℂ => (polynomial n).eval w)=value n := funext (polynomial_eval n)
  have hd := (polynomial n).hasDerivAt w
  rw [he] at hd
  cases n with
  | zero => simp at hroot
  | succ n =>
    have hn := derivative_ne_zero_at_root n w hroot
    rwa [hd.deriv] at hn

theorem polynomial_roots_nodup (n : ℕ) : (polynomial n).roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro w
  rw [Polynomial.count_roots]
  by_contra he
  have hm : 1 < (polynomial n).rootMultiplicity w := by omega
  have hc := (Polynomial.one_lt_rootMultiplicity_iff_isRoot (polynomial_ne_zero n)).mp hm
  exact derivative_eval_ne_zero_at_root n w hc.1 hc.2

def roots (n : ℕ) : Finset ℂ := (polynomial n).roots.toFinset

theorem mem_roots (n : ℕ) (w : ℂ) : w ∈ roots n ↔ value n w=0 := by
  classical
  simp only [roots,Multiset.mem_toFinset,Polynomial.mem_roots (polynomial_ne_zero n),
    Polynomial.IsRoot,polynomial_eval]

theorem card_roots (n : ℕ) : (roots n).card=n := by
  classical
  rw [roots,Multiset.toFinset_card_of_nodup (polynomial_roots_nodup n),
    IsAlgClosed.card_roots_eq_natDegree,polynomial_natDegree]

theorem roots_real (n : ℕ) (w : ℂ) (hw : w ∈ roots n) : w.im=0 :=
  RiemannQuadraticHermite.roots_real n w ((mem_roots n w).mp hw)

theorem roots_nonempty (n : ℕ) (hn : 0 < n) : (roots n).Nonempty := by
  classical
  apply Finset.card_pos.mp
  rwa [card_roots]

theorem at_least_m_simple_zeros_near (m : ℕ) (t : ℝ) (z : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0)
    (hD : iteratedDeriv m (flow 1 t) z ≠ 0) (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ h : ℝ in 𝓝[≠] 0, ∃ S : Finset ℂ, S.card=m ∧
      ∀ ζ ∈ S, ζ ∈ ball z ρ ∧ flow 1 (t+h^2) ζ=0 ∧
        deriv (flow 1 (t+h^2)) ζ ≠ 0 ∧ (z.im=0 → ζ.im=0) := by
  classical
  let I := {a : ℂ // a ∈ roots m}
  letI : Fintype I := inferInstance
  choose r hr C hC hs using (fun a : I =>
    actual_unique_simple_near_model_root m t z a hv hD ((mem_roots m a).mp a.property))
  let W : ℝ → I → ℂ := fun h a =>
    if he : ∃ w, w ∈ closedBall (a : ℂ) (r a) ∧ flow 1 (t+h^2) (z+(h : ℂ)*w)=0
    then Classical.choose he else a
  have hspec (a : I) : ∀ᶠ h : ℝ in 𝓝[≠] 0,
      flow 1 (t+h^2) (z+(h : ℂ)*W h a)=0 ∧
      deriv (flow 1 (t+h^2)) (z+(h : ℂ)*W h a) ≠ 0 ∧
      ‖W h a-(a : ℂ)‖ ≤ C a*|h| ∧ (z.im=0 → (z+(h : ℂ)*W h a).im=0) := by
    filter_upwards [hs a] with h hh
    have hex := hh.1.exists
    have hw : W h a ∈ closedBall (a : ℂ) (r a) ∧ flow 1 (t+h^2) (z+(h : ℂ)*W h a)=0 := by
      dsimp only [W]
      rw [dite_eq_left hex]
      exact Classical.choose_spec hex
    have hlocal := hh.2 (W h a) hw.1 hw.2
    refine ⟨hw.2,hlocal.1,hlocal.2,?_⟩
    intro hz
    have hzeq : (z.re : ℂ)=z := by apply Complex.ext <;> simp [hz]
    have hu : ∃! w, w ∈ closedBall (a : ℂ) (r a) ∧
        flow 1 (t+h^2) ((z.re : ℂ)+(h : ℂ)*w)=0 := by
      simpa only [hzeq] using hh.1
    have hzero : flow 1 (t+h^2) ((z.re : ℂ)+(h : ℂ)*W h a)=0 := by
      simpa only [hzeq] using hw.2
    have him := actual_root_real_of_unique (t+h^2) z.re h a (r a)
      (roots_real m a a.property) hu (W h a) hw.1 hzero
    simp [Complex.add_im,Complex.mul_im,hz,him]
  have habs : Tendsto (fun h : ℝ => |h|) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim (a : I) : Tendsto (fun h : ℝ => W h a) (𝓝[≠] 0) (𝓝 (a : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hbound : Tendsto (fun h : ℝ => C a*|h|) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul habs
    filter_upwards [hspec a,hbound.eventually (Iio_mem_nhds hε)] with h hh hsmall
    rw [dist_eq_norm]
    exact hh.2.2.1.trans_lt hsmall
  have hpairs : ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ a b : I, a ≠ b → W h a ≠ W h b := by
    apply Filter.eventually_all.mpr
    intro a
    apply Filter.eventually_all.mpr
    intro b
    by_cases hab : a=b
    · exact Eventually.of_forall (fun _ hn => (hn hab).elim)
    · have hval : (a : ℂ) ≠ b := fun he => hab (Subtype.ext he)
      have hd := (hlim a).dist (hlim b)
      exact (hd.eventually (Ioi_mem_nhds (dist_pos.mpr hval))).mono
        (fun _ hh _ => dist_pos.mp hh)
  have hphysical (a : I) : Tendsto (fun h : ℝ => z+(h : ℂ)*W h a) (𝓝[≠] 0) (𝓝 z) := by
    have hc : Tendsto (fun h : ℝ => (h : ℂ)) (𝓝[≠] 0) (𝓝 0) := by
      simpa only [Complex.ofReal_zero] using
        (Complex.continuous_ofReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    simpa only [zero_mul,add_zero] using tendsto_const_nhds.add (hc.mul (hlim a))
  have hmem : ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ a : I, z+(h : ℂ)*W h a ∈ ball z ρ :=
    Filter.eventually_all.mpr (fun a => (hphysical a).eventually (ball_mem_nhds z hρ))
  have hall : ∀ᶠ h : ℝ in 𝓝[≠] 0, ∀ a : I,
      flow 1 (t+h^2) (z+(h : ℂ)*W h a)=0 ∧
      deriv (flow 1 (t+h^2)) (z+(h : ℂ)*W h a) ≠ 0 ∧
      ‖W h a-(a : ℂ)‖ ≤ C a*|h| ∧ (z.im=0 → (z+(h : ℂ)*W h a).im=0) :=
    Filter.eventually_all.mpr hspec
  filter_upwards [hpairs,hmem,hall,self_mem_nhdsWithin] with h hpair hmem hall hne
  have hc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by simpa using hne)
  have hinj : Function.Injective (fun a : I => z+(h : ℂ)*W h a) := by
    intro a b he
    have hw : W h a=W h b := mul_left_cancel₀ hc (add_left_cancel he)
    by_contra hn
    exact hpair a b hn hw
  refine ⟨Finset.univ.image (fun a : I => z+(h : ℂ)*W h a),?_,?_⟩
  · rw [Finset.card_image_of_injective Finset.univ hinj,Finset.card_univ]
    simpa only [I,Fintype.card_coe] using card_roots m
  · intro ζ hζ
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hζ
    exact ⟨hmem a,(hall a).1,(hall a).2.1,(hall a).2.2.2⟩

theorem phase_joint_remainder_bound (N : ℕ) (c w h : ℂ)
    (hh : ‖h‖*(1+‖w‖) ≤ 1/2) :
    ‖RiemannQuadraticAllOrders.phase w (c*h)-
      ∑ n ∈ Finset.range (N+1), h^n*(c^n*value n w)/(n.factorial : ℂ)‖ ≤
      2*Real.exp (‖c‖+‖c‖^2)*(‖h‖*(1+‖w‖))^(N+1) := by
  let A : ℝ := 1+‖w‖
  have hA : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by dsimp [A]; linarith [norm_nonneg w]
  have hAc : (A : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hp := RiemannQuadraticAllOrders.scaled_phase_remainder_bound N
    (c/(A : ℂ)) w ((A : ℂ)*h) (by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA]
      simpa only [A,mul_comm] using hh)
  have hprod : c/(A : ℂ)*((A : ℂ)*h)=c*h := by field_simp
  have hterm (n : ℕ) : ((A : ℂ)*h)^n*((c/(A : ℂ))^n*value n w)/(n.factorial : ℂ)=
      h^n*(c^n*value n w)/(n.factorial : ℂ) := by
    rw [← mul_assoc,← mul_pow]
    have he : ((A : ℂ)*h)*(c/(A : ℂ))=h*c := by field_simp
    rw [he,mul_pow]
    ring
  rw [hprod] at hp
  simp_rw [hterm] at hp
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA] at hp
  have hnorm : ‖c/(A : ℂ)‖=‖c‖/A := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hA]
  have hc1 : ‖c‖/A ≤ ‖c‖ := div_le_self (norm_nonneg c) hAone
  have hc2 : (‖c‖/A)*‖w‖ ≤ ‖c‖ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hA).mpr
    dsimp [A]
    nlinarith [norm_nonneg c]
  have he : ‖c/(A : ℂ)‖*‖w‖+‖c/(A : ℂ)‖^2 ≤ ‖c‖+‖c‖^2 := by
    rw [hnorm]
    nlinarith [div_nonneg (norm_nonneg c) hA.le]
  apply hp.trans
  rw [mul_comm A ‖h‖]
  change 2*Real.exp _*(‖h‖*A)^(N+1) ≤ 2*Real.exp _*(‖h‖*A)^(N+1)
  gcongr

theorem jet_joint_expansion_bound (N j : ℕ) (t h : ℝ) (z w : ℂ)
    (hh : |h| *(1+‖w‖) ≤ 1/2) :
    ‖RiemannEvenFlow.jet 1 j (t+h^2) (z+(h : ℂ)*w)-
      ∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n w/(n.factorial : ℂ)*
        RiemannEvenFlow.jet 1 (j+n) t z‖ ≤
      RiemannQuadraticAllOrders.budget j t z 1*(|h| *(1+‖w‖))^(N+1) := by
  let q := |h| *(1+‖w‖)
  have hi := (RiemannEvenDomain.weighted_integrable 1 j (t+1) (‖z‖+1)).const_mul (2*q^(N+1))
  have hpoint : ∀ᵐ u ∂RiemannQuarticFlow.halfLine,
      ‖RiemannQuadraticAllOrders.remainder N j t z h w u‖ ≤
        2*q^(N+1)*RiemannEvenDomain.weighted 1 j (t+1) (‖z‖+1) u := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with u hu
    have hp := phase_joint_remainder_bound N (Complex.I*(u : ℂ)) w (h : ℂ)
      (by simpa only [Complex.norm_real,Real.norm_eq_abs] using hh)
    simp only [norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ u from hu)] at hp
    rw [RiemannQuadraticAllOrders.remainder_factor,norm_mul]
    calc
      _ ≤ RiemannEvenDomain.weighted 1 j t ‖z‖ u*
          (2*Real.exp (u+u^2)*q^(N+1)) :=
        mul_le_mul (RiemannEvenFlow.integrand_bound 1 j t z u hu) hp (norm_nonneg _)
          (RiemannEvenFlow.weighted_nonneg 1 j t ‖z‖ u hu)
      _ = _ := by
        unfold RiemannEvenDomain.weighted
        rw [show (t+1)*u^(2*1)+(‖z‖+1)*u=(t*u^(2*1)+‖z‖*u)+(u+u^2) by ring]
        simp only [Real.exp_add]
        ring
  have hb := MeasureTheory.norm_integral_le_of_norm_le hi hpoint
  rw [RiemannQuadraticAllOrders.remainder_integral,MeasureTheory.integral_const_mul] at hb
  convert hb using 1 <;> dsimp [RiemannQuadraticAllOrders.budget,q] <;> ring

theorem flow_joint_expansion_bound (N : ℕ) (t h : ℝ) (z w : ℂ)
    (hh : |h| *(1+‖w‖) ≤ 1/2) :
    ‖flow 1 (t+h^2) (z+(h : ℂ)*w)-RiemannQuadraticAllOrders.polynomialPart N t z h w‖ ≤
      RiemannQuadraticAllOrders.budget 0 t z 1*(|h| *(1+‖w‖))^(N+1) := by
  have hp := jet_joint_expansion_bound N 0 t h z w hh
  have hn := jet_joint_expansion_bound N 0 t h (-z) (-w) (by simpa only [norm_neg] using hh)
  rw [show -z+(h : ℂ)*(-w)=-(z+(h : ℂ)*w) by ring] at hn
  let ep := jet 1 0 (t+h^2) (z+(h : ℂ)*w)-
    ∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n w/(n.factorial : ℂ)*jet 1 n t z
  let en := jet 1 0 (t+h^2) (-(z+(h : ℂ)*w))-
    ∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n (-w)/(n.factorial : ℂ)*jet 1 n t (-z)
  have hep : ‖ep‖ ≤ RiemannQuadraticAllOrders.budget 0 t z 1*(|h| *(1+‖w‖))^(N+1) := by
    simpa only [ep,Nat.zero_add] using hp
  have hen : ‖en‖ ≤ RiemannQuadraticAllOrders.budget 0 t z 1*(|h| *(1+‖w‖))^(N+1) := by
    simpa only [en,Nat.zero_add,RiemannQuadraticAllOrders.budget,norm_neg] using hn
  have hs : RiemannQuadraticAllOrders.polynomialPart N t z h w =
      ((∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n w/(n.factorial : ℂ)*jet 1 n t z)+
        ∑ n ∈ Finset.range (N+1), (h : ℂ)^n*value n (-w)/(n.factorial : ℂ)*jet 1 n t (-z))/2 := by
    rw [← Finset.sum_add_distrib,Finset.sum_div]
    unfold RiemannQuadraticAllOrders.polynomialPart
    apply Finset.sum_congr rfl
    intro n hn
    rw [RiemannEvenEvolution.flow_iteratedDeriv]
    simp only [RiemannEvenEvolution.symmetricJet,RiemannQuadraticAllOrders.value_neg]
    ring
  have he : flow 1 (t+h^2) (z+(h : ℂ)*w)-RiemannQuadraticAllOrders.polynomialPart N t z h w=(ep+en)/2 := by
    rw [hs]
    dsimp [flow,ep,en]
    ring
  rw [he,norm_div,Complex.norm_ofNat]
  have ha := norm_add_le ep en
  linarith

theorem physical_multiplicity_remainder (m : ℕ) (t h : ℝ) (z v : ℂ)
    (hv : ∀ n < m, iteratedDeriv n (flow 1 t) z=0) (hne : h ≠ 0)
    (hsmall : |h|+‖v‖ ≤ 1/2) :
    ‖flow 1 (t+h^2) (z+v)-
      (h : ℂ)^m*(value m (v/(h : ℂ))/(m.factorial : ℂ)*iteratedDeriv m (flow 1 t) z)‖ ≤
      RiemannQuadraticAllOrders.budget 0 t z 1*(|h|+‖v‖)^(m+1) := by
  have hc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hne
  have hh : |h| ≠ 0 := abs_ne_zero.mpr hne
  have he : |h| *(1+‖v/(h : ℂ)‖)=|h|+‖v‖ := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs]
    field_simp
  have hw : z+(h : ℂ)*(v/(h : ℂ))=z+v := by field_simp
  have hp := flow_joint_expansion_bound m t h z (v/(h : ℂ)) (by rwa [he])
  rw [RiemannQuadraticAllOrders.polynomialPart_at_multiplicity m t z h (v/(h : ℂ)) hv,
    hw,he] at hp
  exact hp

end OperatorDerivativeRewrite.Foundation.RiemannQuadraticCluster
