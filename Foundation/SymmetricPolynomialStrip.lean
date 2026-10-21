import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Multiset
import Mathlib.Algebra.Polynomial.Splits

noncomputable section
open Polynomial Complex Set Filter
open scoped ComplexConjugate
/-! Global zero-strip contraction for symmetric imaginary polynomial shifts.
The proof independently formalizes the classical de Bruijn finite-shift argument
(The roots of trigonometric integrals, 1950, Lemma 1 and Theorems 3--5,
pp. 200--202; https://pure.tue.nl/ws/files/1769368/597490.pdf).
Root multisets retain all multiplicities. Finite iterates are controlled globally;
no unproved scaling limit to Gaussian heat or actual Xi zero transfer is used. -/
namespace OperatorDerivativeRewrite.Foundation.SymmetricPolynomialStrip

theorem pair_normSq_difference (z a : ℂ) (h : ℝ) :
    normSq (z+I*h-a)*normSq (z+I*h-conj a)-
      normSq (z-I*h-a)*normSq (z-I*h-conj a)=
      8*h*z.im*((z.re-a.re)^2+z.im^2+h^2-a.im^2) := by
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,
    Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.conj_re,Complex.conj_im]
  ring

theorem pair_shift_strict (z a : ℂ) (h : ℝ) (hh : 0<h) (hz : 0<z.im)
    (ha : a.im^2<z.im^2+h^2) :
    normSq (z-I*h-a)*normSq (z-I*h-conj a)<
      normSq (z+I*h-a)*normSq (z+I*h-conj a) := by
  have hp : 0<8*h*z.im*((z.re-a.re)^2+z.im^2+h^2-a.im^2) := by
    have hs := sq_nonneg (z.re-a.re)
    have hb : 0<(z.re-a.re)^2+z.im^2+h^2-a.im^2 := by linarith
    positivity
  linarith [pair_normSq_difference z a h]

theorem product_strict_nonneg {α : Type*} (L : Multiset α) (hL : L≠0)
    (f g : α → ℝ) (hf : ∀ a∈L,0≤f a) (hlt : ∀ a∈L,f a<g a) :
    (L.map f).prod<(L.map g).prod := by
  obtain ⟨a,ha⟩ := Multiset.exists_mem_of_ne_zero hL
  obtain ⟨S,rfl⟩ := Multiset.exists_cons_of_mem ha
  have hfa := hf a (Multiset.mem_cons_self a S)
  have hga := hlt a (Multiset.mem_cons_self a S)
  have hrest := Multiset.prod_map_le_prod_map₀ f g
    (fun b hb => hf b (Multiset.mem_cons_of_mem hb))
    (fun b hb => (hlt b (Multiset.mem_cons_of_mem hb)).le)
  have hgpos : 0<(S.map g).prod := Multiset.prod_pos (by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := Multiset.mem_map.mp hv
    exact lt_of_le_of_lt (hf b (Multiset.mem_cons_of_mem hb))
      (hlt b (Multiset.mem_cons_of_mem hb)))
  simp only [Multiset.map_cons,Multiset.prod_cons]
  exact (mul_le_mul_of_nonneg_left hrest hfa).trans_lt (mul_lt_mul_of_pos_right hga hgpos)

def rootProduct (L : Multiset ℂ) (z : ℂ) : ℂ := (L.map (fun a => z-a)).prod

theorem normSq_rootProduct (L : Multiset ℂ) (z : ℂ) :
    normSq (rootProduct L z)=(L.map (fun a => normSq (z-a))).prod := by
  induction L using Multiset.induction_on with
  | empty => simp [rootProduct]
  | cons a L ih => simpa [rootProduct,normSq_mul] using congrArg (fun t : ℝ => normSq (z-a)*t) ih

theorem root_product_shift_strict (L : Multiset ℂ) (hL : L≠0)
    (hc : L.map conj=L) (z : ℂ) (h b : ℝ) (hh : 0<h) (hz : 0<z.im)
    (hb : ∀ a∈L,a.im^2≤b^2) (hout : b^2<z.im^2+h^2) :
    normSq (rootProduct L (z-I*h))<normSq (rootProduct L (z+I*h)) := by
  let f : ℂ → ℝ := fun a => normSq (z-I*h-a)
  let g : ℂ → ℝ := fun a => normSq (z+I*h-a)
  have hp := product_strict_nonneg L hL (fun a => f a*f (conj a))
    (fun a => g a*g (conj a))
    (fun a _ => mul_nonneg (normSq_nonneg _) (normSq_nonneg _))
    (fun a ha => pair_shift_strict z a h hh hz (lt_of_le_of_lt (hb a ha) hout))
  have hf : (L.map (fun a => f (conj a))).prod=(L.map f).prod := by
    simpa only [Multiset.map_map,Function.comp_def] using congrArg (fun S : Multiset ℂ => (S.map f).prod) hc
  have hg : (L.map (fun a => g (conj a))).prod=(L.map g).prod := by
    simpa only [Multiset.map_map,Function.comp_def] using congrArg (fun S : Multiset ℂ => (S.map g).prod) hc
  rw [Multiset.prod_map_mul,Multiset.prod_map_mul,hf,hg] at hp
  rw [normSq_rootProduct,normSq_rootProduct]
  have hn := Multiset.prod_map_nonneg (s:=L) (fun a _ => normSq_nonneg (z-I*h-a))
  have hm := Multiset.prod_map_nonneg (s:=L) (fun a _ => normSq_nonneg (z+I*h-a))
  dsimp [f,g] at hp
  nlinarith

theorem polynomial_roots_conj (P : ℂ[X]) (hc : P.map (starRingEnd ℂ)=P) :
    P.roots.map conj=P.roots := by
  have he := (IsAlgClosed.splits P).roots_map_of_injective
    (i:=starRingEnd ℂ) (starRingEnd ℂ).injective
  rw [hc] at he
  exact he.symm

theorem polynomial_root_product (P : ℂ[X]) (z : ℂ) :
    P.eval z=P.leadingCoeff*rootProduct P.roots z := by
  have he := congrArg (fun Q : ℂ[X] => Q.eval z)
    (P.C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.splits P).natDegree_eq_card_roots.symm)
  simpa [eval_multiset_prod,Multiset.map_map,Function.comp_def,rootProduct] using he.symm

theorem polynomial_shift_strict (P : ℂ[X]) (hp : P≠0) (hd : P.natDegree≠0)
    (hc : P.map (starRingEnd ℂ)=P) (z : ℂ) (h b : ℝ) (hh : 0<h) (hz : 0<z.im)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) (hout : b^2<z.im^2+h^2) :
    normSq (P.eval (z-I*h))<normSq (P.eval (z+I*h)) := by
  have hr := root_product_shift_strict P.roots ((IsAlgClosed.splits P).roots_ne_zero hd)
    (polynomial_roots_conj P hc) z h b hh hz
    (fun a ha => hb a ((Polynomial.mem_roots hp).mp ha)) hout
  rw [polynomial_root_product,polynomial_root_product,normSq_mul,normSq_mul]
  exact mul_lt_mul_of_pos_left hr (normSq_pos.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))

def symmetricShift (h : ℝ) (P : ℂ[X]) : ℂ[X] :=
  C (1/2)*(P.comp (X+C (I*h))+P.comp (X-C (I*h)))

theorem symmetricShift_eval (h : ℝ) (P : ℂ[X]) (z : ℂ) :
    (symmetricShift h P).eval z=(P.eval (z+I*h)+P.eval (z-I*h))/2 := by
  simp [symmetricShift,div_eq_mul_inv,mul_comm]

theorem symmetricShift_conj (h : ℝ) (P : ℂ[X])
    (hc : P.map (starRingEnd ℂ)=P) :
    (symmetricShift h P).map (starRingEnd ℂ)=symmetricShift h P := by
  simp only [symmetricShift,Polynomial.map_mul,Polynomial.map_C,map_div₀,map_one,map_ofNat,
    Polynomial.map_add,Polynomial.map_comp,Polynomial.map_sub,Polynomial.map_X,hc,
    map_mul,Complex.conj_I,Complex.conj_ofReal,neg_mul]
  simp only [map_neg,sub_neg_eq_add,← sub_eq_add_neg]
  ring

theorem symmetricShift_upper_ne_zero (P : ℂ[X]) (hp : P≠0)
    (hc : P.map (starRingEnd ℂ)=P) (z : ℂ) (h b : ℝ) (hh : 0<h) (hz : 0<z.im)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) (hout : b^2<z.im^2+h^2) :
    (symmetricShift h P).eval z≠0 := by
  by_cases hd : P.natDegree=0
  · have he : P=C (P.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hd
    have hn : P.coeff 0≠0 := by intro hz; rw [he,hz,Polynomial.C_0] at hp; exact hp rfl
    rw [symmetricShift_eval,he]
    simpa using hn
  · have hs := polynomial_shift_strict P hp hd hc z h b hh hz hb hout
    intro he
    rw [symmetricShift_eval] at he
    have hzsum : P.eval (z+I*h)= -P.eval (z-I*h) := by
      apply eq_neg_iff_add_eq_zero.mpr
      exact (div_eq_zero_iff.mp he).resolve_right (by norm_num)
    rw [hzsum,normSq_neg] at hs
    exact (lt_irrefl _) hs

theorem symmetricShift_zero_strip (P : ℂ[X]) (hp : P≠0)
    (hc : P.map (starRingEnd ℂ)=P) (h b : ℝ) (hh : 0<h)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) (z : ℂ)
    (hz : (symmetricShift h P).eval z=0) : z.im^2≤max (b^2-h^2) 0 := by
  by_contra hn
  have hout : max (b^2-h^2) 0<z.im^2 := lt_of_not_ge hn
  have hpos : 0<z.im^2 := lt_of_le_of_lt (le_max_right _ _) hout
  have hbz : b^2<z.im^2+h^2 := by have hm:=le_max_left (b^2-h^2) 0; linarith
  rcases lt_or_gt_of_ne (show z.im≠0 by intro he; rw [he] at hpos; norm_num at hpos) with hi|hi
  · have hzconj : (symmetricShift h P).eval (conj z)=0 := by
      have he := Polynomial.eval_map_apply (p:=symmetricShift h P) (f:=starRingEnd ℂ) z
      rw [symmetricShift_conj h P hc,hz] at he
      simpa using he
    exact symmetricShift_upper_ne_zero P hp hc (conj z) h b hh (by simpa using neg_pos.mpr hi)
      hb (by simpa using hbz) hzconj
  · exact symmetricShift_upper_ne_zero P hp hc z h b hh hi hb hbz hz

theorem symmetricShift_ne_zero (P : ℂ[X]) (hp : P≠0)
    (hc : P.map (starRingEnd ℂ)=P) (h b : ℝ) (hh : 0<h)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) : symmetricShift h P≠0 := by
  have he := symmetricShift_upper_ne_zero P hp hc (I*((b^2+1:ℝ):ℂ)) h b hh
    (by simpa only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,one_mul,zero_add] using (by positivity : 0<b^2+1)) hb
    (by simp only [Complex.mul_im,Complex.I_re,Complex.I_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,one_mul,zero_add]
        nlinarith [sq_nonneg b,sq_nonneg h])
  intro hz
  exact he (by rw [hz]; simp)

def iteratedShift (h : ℝ) (n : ℕ) (P : ℂ[X]) : ℂ[X] := (symmetricShift h)^[n] P

theorem max_budget_step (B q : ℝ) (hq : 0≤q) :
    max (max B 0-q) 0=max (B-q) 0 := by
  by_cases hB : 0≤B
  · rw [max_eq_left hB]
  · rw [max_eq_right (le_of_not_ge hB),zero_sub,
      max_eq_right (neg_nonpos.mpr hq),max_eq_right (by linarith)]

theorem iteratedShift_properties (P : ℂ[X]) (hp : P≠0)
    (hc : P.map (starRingEnd ℂ)=P) (h b : ℝ) (hh : 0<h)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) (n : ℕ) :
    iteratedShift h n P≠0 ∧
      (iteratedShift h n P).map (starRingEnd ℂ)=iteratedShift h n P ∧
      ∀ z : ℂ,(iteratedShift h n P).eval z=0 → z.im^2≤max (b^2-(n:ℝ)*h^2) 0 := by
  induction n with
  | zero =>
    refine ⟨hp,hc,?_⟩
    intro z hz
    simpa [max_eq_left (sq_nonneg b)] using hb z hz
  | succ n ih =>
    let B : ℝ := max (b^2-(n:ℝ)*h^2) 0
    have hB : 0≤B := le_max_right _ _
    have hs : (Real.sqrt B)^2=B := Real.sq_sqrt hB
    have hbound (z : ℂ) (hz : (iteratedShift h n P).eval z=0) :
        z.im^2≤(Real.sqrt B)^2 := by rw [hs]; exact ih.2.2 z hz
    simp only [iteratedShift,Function.iterate_succ_apply']
    refine ⟨symmetricShift_ne_zero _ ih.1 ih.2.1 h (Real.sqrt B) hh hbound,
      symmetricShift_conj h _ ih.2.1,?_⟩
    intro z hz
    have he := symmetricShift_zero_strip _ ih.1 ih.2.1 h (Real.sqrt B) hh hbound z hz
    rw [hs] at he
    dsimp [B] at he
    rw [max_budget_step _ _ (sq_nonneg h)] at he
    convert he using 1 <;> push_cast <;> ring

theorem iteratedShift_real_roots (P : ℂ[X]) (hp : P≠0)
    (hc : P.map (starRingEnd ℂ)=P) (h b : ℝ) (hh : 0<h)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) (n : ℕ)
    (hn : b^2≤(n:ℝ)*h^2) (z : ℂ)
    (hz : (iteratedShift h n P).eval z=0) : z.im=0 := by
  have he := (iteratedShift_properties P hp hc h b hh hb n).2.2 z hz
  rw [max_eq_right (sub_nonpos.mpr hn)] at he
  nlinarith [sq_nonneg z.im]

def scaledShift (s : ℝ) (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  iteratedShift (Real.sqrt (2*s/((n+1:ℕ):ℝ))) (n+1) P

theorem scaledShift_properties (P : ℂ[X]) (hp : P≠0)
    (hc : P.map (starRingEnd ℂ)=P) (s b : ℝ) (hs : 0<s)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) (n : ℕ) :
    scaledShift s n P≠0 ∧
      (scaledShift s n P).map (starRingEnd ℂ)=scaledShift s n P ∧
      ∀ z : ℂ,(scaledShift s n P).eval z=0 → z.im^2≤max (b^2-2*s) 0 := by
  have hd : (0:ℝ)<((n+1:ℕ):ℝ) := by positivity
  have ht : 0<2*s/((n+1:ℕ):ℝ) := div_pos (by positivity) hd
  have he := iteratedShift_properties P hp hc (Real.sqrt (2*s/((n+1:ℕ):ℝ))) b
    (Real.sqrt_pos.mpr ht) hb (n+1)
  have hclock : ((n+1:ℕ):ℝ)*(Real.sqrt (2*s/((n+1:ℕ):ℝ)))^2=2*s := by
    rw [Real.sq_sqrt ht.le]
    field_simp
  rw [hclock] at he
  exact he

theorem real_map_conj (P : ℝ[X]) :
    (P.map (algebraMap ℝ ℂ)).map (starRingEnd ℂ)=P.map (algebraMap ℝ ℂ) := by
  ext n
  simp

theorem scaledShift_real_polynomial (P : ℝ[X]) (hp : P≠0) (s b : ℝ) (hs : 0<s)
    (hb : ∀ a : ℂ,(P.map (algebraMap ℝ ℂ)).eval a=0 → a.im^2≤b^2) (n : ℕ) :
    scaledShift s n (P.map (algebraMap ℝ ℂ))≠0 ∧
      (scaledShift s n (P.map (algebraMap ℝ ℂ))).map (starRingEnd ℂ)=
        scaledShift s n (P.map (algebraMap ℝ ℂ)) ∧
      ∀ z : ℂ,(scaledShift s n (P.map (algebraMap ℝ ℂ))).eval z=0 →
        z.im^2≤max (b^2-2*s) 0 :=
  scaledShift_properties _ ((Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hp)
    (real_map_conj P) s b hs hb n

theorem scaledShift_real_roots (P : ℂ[X]) (hp : P≠0)
    (hc : P.map (starRingEnd ℂ)=P) (s b : ℝ) (hs : 0<s)
    (hb : ∀ a : ℂ,P.eval a=0 → a.im^2≤b^2) (n : ℕ) (ht : b^2≤2*s) (z : ℂ)
    (hz : (scaledShift s n P).eval z=0) : z.im=0 := by
  have he := (scaledShift_properties P hp hc s b hs hb n).2.2 z hz
  rw [max_eq_right (sub_nonpos.mpr ht)] at he
  nlinarith [sq_nonneg z.im]

end OperatorDerivativeRewrite.Foundation.SymmetricPolynomialStrip
