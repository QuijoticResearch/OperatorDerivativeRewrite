import Foundation.PeriodicChargedFourier
/-! Complete charged Fourier synthesis on the ACTUAL period-four spatial
lattice. Exact inverse transforms, Parseval and shift diagonalization yield the
actual Wilson charged Hessian decomposition. At nontrivial adjoint holonomy its
charged kernel is exactly the actual charged gauge-gradient range. Neutral
colors, singular harmonic modes, global gauge quotients, temporal integration
and native stationary spectral limits are not identified by these statements. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.PeriodicChargedSynthesis
open PeriodicTemporalSlab PeriodicChargedFourier

theorem root_gram (n m : ZMod 4) :
    (∑ j : ZMod 4,starRingEnd ℂ (root4 (n*j))*root4 (m*j))=if n=m then 4 else 0 := by
  have h : ∀ n m : Fin 4,
      (∑ j : Fin 4,starRingEnd ℂ (root4 (n*j))*root4 (m*j))=if n=m then 4 else 0 := by
    intro n m
    change (∑ j : Fin 4,starRingEnd ℂ (Complex.I^(n*j).val)*Complex.I^(m*j).val)=_
    fin_cases n <;> fin_cases m <;> norm_num [Fin.sum_univ_succ,Fin.mul_def,pow_succ]
  exact h n m

theorem gram (k l : Frequency) :
    (∑ v : SpatialVertex,starRingEnd ℂ (character k v)*character l v)=
      if k=l then 64 else 0 := by
  simp only [character,map_prod,← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin 3) (j : ZMod 4) => starRingEnd ℂ (root4 (k i*j))*root4 (l i*j))]
  simp_rw [root_gram]
  by_cases h : k=l
  · subst l
    norm_num
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i,k i≠l i := by
      by_contra hn
      push Not at hn
      exact h (funext hn)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact if_neg hi

theorem character_comm (k v : Frequency) : character k v=character v k := by
  unfold character
  simp_rw [mul_comm]

theorem dual_gram (v w : SpatialVertex) :
    (∑ k : Frequency,character k v*starRingEnd ℂ (character k w))=
      if v=w then 64 else 0 := by
  calc
    _ = ∑ k : Frequency,starRingEnd ℂ (character w k)*character v k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [character_comm k v,character_comm k w,mul_comm]
    _ = _ := by rw [gram]; by_cases h : v=w <;> simp [h,eq_comm]

def coefficients (f : SpatialVertex → ℂ) (k : Frequency) : ℂ :=
  (64 : ℂ)⁻¹*∑ v,starRingEnd ℂ (character k v)*f v

def synthesis (a : Frequency → ℂ) (v : SpatialVertex) : ℂ :=
  ∑ k,character k v*a k

theorem reconstruction (f : SpatialVertex → ℂ) : synthesis (coefficients f)=f := by
  funext v
  unfold synthesis coefficients
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hr (w : SpatialVertex) :
      (∑ k : Frequency,character k v*((64 : ℂ)⁻¹*(starRingEnd ℂ (character k w)*f w)))=
      (64 : ℂ)⁻¹*(∑ k : Frequency,character k v*starRingEnd ℂ (character k w))*f w := by
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [hr,dual_gram]
  simp

theorem coefficient_synthesis (a : Frequency → ℂ) : coefficients (synthesis a)=a := by
  funext k
  change (64 : ℂ)⁻¹*(∑ v : SpatialVertex,starRingEnd ℂ (character k v)*(∑ l,character l v*a l))=a k
  have hp : (∑ v : SpatialVertex,starRingEnd ℂ (character k v)*(∑ l,character l v*a l))=64*a k := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc,← Finset.sum_mul,gram]
    simp
  rw [hp]
  ring

theorem synthesis_pairing (a b : Frequency → ℂ) :
    (∑ v : SpatialVertex,starRingEnd ℂ (synthesis a v)*synthesis b v)=
      64*∑ k,starRingEnd ℂ (a k)*b k := by
  have hr (v : SpatialVertex) : starRingEnd ℂ (synthesis a v)*synthesis b v=
      ∑ k : Frequency,∑ l : Frequency,
        (starRingEnd ℂ (a k)*b l)*(starRingEnd ℂ (character k v)*character l v) := by
    simp only [synthesis,map_sum,map_mul,Finset.sum_mul,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hr]
  rw [Finset.sum_comm]
  have hs (k : Frequency) :
      (∑ v : SpatialVertex,∑ l : Frequency,
        (starRingEnd ℂ (a k)*b l)*(starRingEnd ℂ (character k v)*character l v))=
      ∑ l : Frequency,(starRingEnd ℂ (a k)*b l)*(if k=l then 64 else 0) := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum,gram]
  simp_rw [hs]
  simp only [mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem synthesis_parseval (a : Frequency → ℂ) :
    (∑ v : SpatialVertex,Complex.normSq (synthesis a v))=64*∑ k,Complex.normSq (a k) := by
  have h := synthesis_pairing a a
  simp_rw [← Complex.normSq_eq_conj_mul_self] at h
  exact_mod_cast h

theorem parseval (f : SpatialVertex → ℂ) :
    (∑ v,Complex.normSq (f v))=64*∑ k,Complex.normSq (coefficients f k) := by
  simpa only [reconstruction] using synthesis_parseval (coefficients f)

theorem coefficients_injective : Function.Injective coefficients := by
  intro f g h
  calc
    f = synthesis (coefficients f) := (reconstruction f).symm
    _ = synthesis (coefficients g) := congrArg synthesis h
    _ = g := reconstruction g

theorem coefficients_add (f g : SpatialVertex → ℂ) (k : Frequency) :
    coefficients (fun v => f v+g v) k=coefficients f k+coefficients g k := by
  simp [coefficients,mul_add,Finset.sum_add_distrib]

theorem coefficients_sub (f g : SpatialVertex → ℂ) (k : Frequency) :
    coefficients (fun v => f v-g v) k=coefficients f k-coefficients g k := by
  simp [coefficients,mul_sub,Finset.sum_sub_distrib]

theorem coefficients_mul (c : ℂ) (f : SpatialVertex → ℂ) (k : Frequency) :
    coefficients (fun v => c*f v) k=c*coefficients f k := by
  unfold coefficients
  simp_rw [mul_left_comm _ c,← Finset.mul_sum]
  ring

def transform : (SpatialVertex → ℂ) ≃ₗ[ℂ] (Frequency → ℂ) where
  toFun := coefficients
  invFun := synthesis
  left_inv := reconstruction
  right_inv := coefficient_synthesis
  map_add' f g := funext (coefficients_add f g)
  map_smul' c f := by
    funext k
    exact coefficients_mul c f k

theorem synthesis_shift (a : Frequency → ℂ) (v : SpatialVertex) (i : Fin 3) :
    synthesis a (shift v i)=synthesis (fun k => root4 (k i)*a k) v := by
  unfold synthesis
  simp_rw [character_shift]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem coefficients_shift (f : SpatialVertex → ℂ) (k : Frequency) (i : Fin 3) :
    coefficients (fun v => f (shift v i)) k=root4 (k i)*coefficients f k := by
  have hs : (fun v => f (shift v i))=synthesis (fun k => root4 (k i)*coefficients f k) := by
    funext v
    rw [← synthesis_shift,reconstruction]
  rw [hs,coefficient_synthesis]


open SU2GaussianConeCoordinates SU2HemisphereJets SU2RootAdjoint PeriodicFlatBackgroundHessian
open PeriodicWilsonSlab
open PeriodicConstantQuarticJet (Pair3)

def encoded (f : SpatialEdge → ℂ) : Velocity := fun e => lift (f e)
def modeCoefficients (f : SpatialEdge → ℂ) (k : Frequency) (i : Fin 3) : ℂ :=
  coefficients (fun v => f (v,i)) k

theorem field_reconstruction (f : SpatialEdge → ℂ) (e : SpatialEdge) :
    f e=∑ k : Frequency,character k e.1*modeCoefficients f k e.2 := by
  exact (congrFun (reconstruction (fun v => f (v,e.2))) e.1).symm

theorem encoded_covers (X : Velocity) (h : ∀ e,X e 0=0) :
    encoded (fun e => charge (X e))=X := by
  funext e
  ext i
  fin_cases i <;> simp [encoded,lift,charge,h]

def complexCurl (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ)
    (v : SpatialVertex) (i j : Fin 3) : ℂ :=
  f (v,i)+phase (α i)*f (shift v i,j)-phase (α j)*f (shift v j,i)-f (v,j)

theorem curl_encoded (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ)
    (v : SpatialVertex) (i j : Fin 3) :
    covariantCurl (background α) (encoded f) v i j=lift (complexCurl α f v i j) := by
  unfold covariantCurl encoded background complexCurl
  rw [rotate_lift,rotate_lift,← lift_add,← lift_sub,← lift_sub]

theorem coefficients_curl (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ)
    (k : Frequency) (i j : Fin 3) :
    coefficients (fun v => complexCurl α f v i j) k=
      delta α k i*modeCoefficients f k j-delta α k j*modeCoefficients f k i := by
  unfold complexCurl
  rw [coefficients_sub,coefficients_sub,coefficients_add,coefficients_mul,coefficients_mul,
    coefficients_shift (fun v => f (v,j)) k i,coefficients_shift (fun v => f (v,i)) k j]
  unfold delta modeCoefficients
  ring

private def faceEquiv : SpatialFace ≃ SpatialVertex × Pair3 where
  toFun p := (p.val.1,⟨p.val.2,p.property⟩)
  invFun p := ⟨(p.1,p.2.val),p.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem quadratic_decomposition (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ) :
    PeriodicFlatBackgroundHessian.quadratic (background α) (encoded f)=
      64*∑ k : Frequency,pairEnergy (delta α k) (modeCoefficients f k) := by
  unfold PeriodicFlatBackgroundHessian.quadratic
  simp_rw [curl_encoded,lift_size]
  rw [← faceEquiv.symm.sum_comp]
  simp only [Fintype.sum_prod_type,faceEquiv,Equiv.coe_fn_symm_mk]
  rw [Finset.sum_comm]
  have hp (p : Pair3) :
      (∑ v : SpatialVertex,Complex.normSq (complexCurl α f v p.val.1 p.val.2))=
      64*∑ k : Frequency,Complex.normSq
        (delta α k p.val.1*modeCoefficients f k p.val.2-
          delta α k p.val.2*modeCoefficients f k p.val.1) := by
    rw [parseval]
    simp_rw [coefficients_curl]
  simp_rw [hp]
  rw [← Finset.mul_sum,Finset.sum_comm]
  rfl

theorem size_decomposition (f : SpatialEdge → ℂ) :
    (∑ e : SpatialEdge,sizeSq (encoded f e))=
      64*∑ k : Frequency,total (modeCoefficients f k) := by
  simp only [encoded,lift_size,Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have hp (i : Fin 3) :
      (∑ v : SpatialVertex,Complex.normSq (f (v,i)))=
      64*∑ k : Frequency,Complex.normSq (modeCoefficients f k i) := parseval _
  simp_rw [hp]
  rw [← Finset.mul_sum,Finset.sum_comm]
  rfl

theorem spatial_second_decomposition (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ) :
    deriv (deriv (fun t : ℝ => spatialAction (state (background α) (encoded f) t))) 0=
      64*∑ k : Frequency,
        (symbolSize α k*total (modeCoefficients f k)-
          Complex.normSq (longitudinal (delta α k) (modeCoefficients f k))) := by
  rw [spatial_second _ _ (background_commutes α),quadratic_decomposition]
  simp_rw [hermitian_curl_identity]
  rfl

theorem pairEnergy_nonneg (d a : Fin 3 → ℂ) : 0≤pairEnergy d a := by
  exact Finset.sum_nonneg (fun p _ => Complex.normSq_nonneg _)

theorem minor_zero (d a : Fin 3 → ℂ) (h : pairEnergy d a=0) (i j : Fin 3) :
    d i*a j-d j*a i=0 := by
  have hp (p : Pair3) : d p.val.1*a p.val.2-d p.val.2*a p.val.1=0 := by
    have he := Finset.single_le_sum
      (fun q (_ : q∈Finset.univ) => Complex.normSq_nonneg
        (d q.val.1*a q.val.2-d q.val.2*a q.val.1)) (Finset.mem_univ p)
    change Complex.normSq (d p.val.1*a p.val.2-d p.val.2*a p.val.1)≤pairEnergy d a at he
    exact Complex.normSq_eq_zero.mp (le_antisymm (he.trans_eq h) (Complex.normSq_nonneg _))
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hp ⟨(i,j),hij⟩
  · subst j; ring
  · have he := hp ⟨(j,i),hij⟩
    linear_combination -he

theorem pairEnergy_zero_iff (d a : Fin 3 → ℂ) (hd : ∃ i,d i≠0) :
    pairEnergy d a=0 ↔ ∃ c : ℂ,∀ i,a i=d i*c := by
  constructor
  · intro h
    obtain ⟨j,hj⟩ := hd
    refine ⟨a j/d j,?_⟩
    intro i
    rw [← mul_div_assoc]
    apply (eq_div_iff hj).mpr
    have he := minor_zero d a h i j
    linear_combination -he
  · rintro ⟨c,hc⟩
    have he : a=(fun i => d i*c) := funext hc
    rw [he,parallel_energy_zero]

theorem quadratic_zero_iff (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ) :
    PeriodicFlatBackgroundHessian.quadratic (background α) (encoded f)=0 ↔
      ∀ k : Frequency,pairEnergy (delta α k) (modeCoefficients f k)=0 := by
  rw [quadratic_decomposition]
  have he : (64 : ℝ)≠0 := by norm_num
  simp only [mul_eq_zero,he,false_or]
  exact Finset.sum_eq_zero_iff_of_nonneg (fun k _ => pairEnergy_nonneg _ _) |>.trans (by simp)

theorem noncentral_null_amplitudes (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ)
    (hhol : ∃ i,phase (α i)^4≠1)
    (hQ : PeriodicFlatBackgroundHessian.quadratic (background α) (encoded f)=0) :
    ∃ c : Frequency → ℂ,∀ k i,modeCoefficients f k i=delta α k i*c k := by
  have hp (k : Frequency) : ∃ c : ℂ,∀ i,modeCoefficients f k i=delta α k i*c := by
    apply (pairEnergy_zero_iff _ _ ?_).mp ((quadratic_zero_iff α f).mp hQ k)
    by_contra hn
    push Not at hn
    have hz := (symbolSize_zero_iff α k).mpr hn
    have hpos := symbolSize_pos_of_holonomy α k hhol
    linarith
  exact Classical.skolem.mp hp

theorem gauge_encoded (α : Fin 3 → ℝ) (Z : SpatialVertex → ℂ) :
    gaugeGradient (background α) (fun v => lift (Z v))=
      encoded (fun e => Z e.1-phase (α e.2)*Z (shift e.1 e.2)) := by
  funext e
  unfold gaugeGradient background encoded
  rw [rotate_lift,← lift_sub]

theorem noncentral_null_is_gauge (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ)
    (hhol : ∃ i,phase (α i)^4≠1)
    (hQ : PeriodicFlatBackgroundHessian.quadratic (background α) (encoded f)=0) :
    ∃ Z : SpatialVertex → ℂ,
      gaugeGradient (background α) (fun v => lift (Z v))=encoded f := by
  obtain ⟨c,hc⟩ := noncentral_null_amplitudes α f hhol hQ
  let Z := synthesis (fun k => -c k)
  refine ⟨Z,?_⟩
  rw [gauge_encoded]
  apply congrArg encoded
  funext e
  have he : (fun v => Z v-phase (α e.2)*Z (shift v e.2))=(fun v => f (v,e.2)) := by
    apply coefficients_injective
    funext k
    rw [coefficients_sub,coefficients_mul,coefficients_shift Z k e.2]
    change coefficients (synthesis (fun k => -c k)) k-
      phase (α e.2)*(root4 (k e.2)*coefficients (synthesis (fun k => -c k)) k)=modeCoefficients f k e.2
    rw [coefficient_synthesis,hc]
    unfold delta
    ring
  exact congrFun he e.1

theorem noncentral_null_iff_gauge (α : Fin 3 → ℝ) (f : SpatialEdge → ℂ)
    (hhol : ∃ i,phase (α i)^4≠1) :
    PeriodicFlatBackgroundHessian.quadratic (background α) (encoded f)=0 ↔
      ∃ Z : SpatialVertex → ℂ,
        gaugeGradient (background α) (fun v => lift (Z v))=encoded f := by
  constructor
  · exact noncentral_null_is_gauge α f hhol
  · rintro ⟨Z,hZ⟩
    rw [← hZ]
    exact quadratic_gauge_zero _ _ (background_commutes α)

end OperatorDerivativeRewrite.Foundation.PeriodicChargedSynthesis
