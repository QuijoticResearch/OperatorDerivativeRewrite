import Foundation.FiniteWilsonTorusGap

/-! Centered elementary-plaquette sum in the actual finite homogeneous Z2
stationary law. No SU2, volume-uniform or physical4D assertion is made. -/
noncomputable section
namespace OperatorDerivativeRewrite.Foundation.FiniteWilsonPlaquetteSlowing
open FiniteWilsonTorusKernel FiniteWilsonTorusStationary FiniteWilsonTorusProbe

private def scoreAt : Fin 4 → ℝ := ![4,0,0,-4]

def score (i : State) : ℝ := scoreAt (orbit i)

def centered (f : State → ℝ) (i : State) : ℝ := f i-mean f

theorem score_microscopic (u : Fin 256) :
    score (FiniteWilsonTorusNoise.labelState u)=(FiniteWilsonTorusNoise.plaquetteScore u:ℝ) := by
  rw [FiniteWilsonTorusNoise.score_certificate]
  unfold score
  generalize orbit (FiniteWilsonTorusNoise.labelState u)=i
  fin_cases i <;> norm_num [score,scoreAt]

theorem score_gauge (g : Fin 8) (u : Fin 256) :
    score (FiniteWilsonTorusNoise.labelState (FiniteWilsonTorusNoise.gaugeAction g u))=
      score (FiniteWilsonTorusNoise.labelState u) := by
  rw [FiniteWilsonTorusNoise.label_gauge]

private theorem average_sub (f : State → ℝ) (c : ℝ) (i : State) :
    average (fun j => f j-c) i=average f i-c := by
  simp only [average,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,step_rows,one_mul]

private theorem mean_average (f : State → ℝ) : mean (average f)=mean f := by
  unfold mean average
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul,stationary_step]

theorem centered_mean (f : State → ℝ) : mean (centered f)=0 := by
  simp only [mean,centered,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,stationary_total,one_mul]
  ring

theorem centered_second (f : State → ℝ) :
    secondMoment (centered f)=secondMoment f-(mean f)^2 := by
  calc
    _ = ∑ i,(stationary i*f i^2-(2*mean f)*(stationary i*f i)+
        (mean f)^2*stationary i) := by
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [centered]
      ring
    _ = secondMoment f-(mean f)^2 := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum]
      change secondMoment f-2*mean f*mean f+(mean f)^2*(∑ i,stationary i)=_
      rw [stationary_total]
      ring

theorem centered_lag (f : State → ℝ) :
    lagPairing (centered f)=lagPairing f-(mean f)^2 := by
  calc
    _ = ∑ i,(stationary i*f i*average f i-mean f*(stationary i*f i)-
        mean f*(stationary i*average f i)+(mean f)^2*stationary i) := by
      unfold lagPairing
      apply Finset.sum_congr rfl
      intro i hi
      change stationary i*(f i-mean f)*average (fun j => f j-mean f) i=_
      rw [average_sub]
      ring
    _ = lagPairing f-(mean f)^2 := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_sub_distrib]
      rw [← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum]
      change lagPairing f-mean f*mean f-mean f*mean (average f)+
        (mean f)^2*(∑ i,stationary i)=_
      rw [mean_average,stationary_total]
      ring

private theorem lag_numerator (f : State → ℝ) :
    lagPairing f=(∑ i,ground i*f i*(∑ j,transfer i j*ground j*f j))/
      (FiniteWilsonTorusGround.value*normalizer) := by
  unfold lagPairing average
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have ha : (∑ j,step i j*f j)=(∑ j,transfer i j*ground j*f j)/
      (FiniteWilsonTorusGround.value*ground i) := by
    simp only [step,div_mul_eq_mul_div,Finset.sum_div]
  rw [ha]
  unfold stationary
  field_simp [normalizer_pos.ne',FiniteWilsonTorusGround.value_pos.ne',(ground_positive i).ne']

private def Z : ℝ := FiniteWilsonTorusGround.normalizer

private theorem normalizer_orbit : normalizer=4*Z := by
  norm_num [normalizer,Z,FiniteWilsonTorusGround.normalizer,
    FiniteWilsonTorusGround.multiplicity,ground,orbit,Fin.sum_univ_succ]
  ring

private theorem Z_pos : 0 < Z := FiniteWilsonTorusGround.normalizer_pos

private def C : ℝ := (3177/2048)*FiniteWilsonTorusGround.ground 0^2-
    2*(225/2048)*FiniteWilsonTorusGround.ground 0*FiniteWilsonTorusGround.ground 3+
    (353/18432)*FiniteWilsonTorusGround.ground 3^2

private theorem score_mean : mean score=4*(FiniteWilsonTorusGround.ground 0^2-
    FiniteWilsonTorusGround.ground 3^2)/Z := by
  norm_num [mean,score,scoreAt,stationary,ground,orbit,Fin.sum_univ_succ]
  rw [normalizer_orbit]
  ring

private theorem score_second : secondMoment score=16*(FiniteWilsonTorusGround.ground 0^2+
    FiniteWilsonTorusGround.ground 3^2)/Z := by
  norm_num [secondMoment,score,scoreAt,stationary,ground,orbit,Fin.sum_univ_succ]
  rw [normalizer_orbit]
  ring

private theorem score_lag : lagPairing score=16*C/(FiniteWilsonTorusGround.value*Z) := by
  rw [lag_numerator]
  have hr (i : State) : (∑ j,transfer i j*ground j*score j)=
      ∑ b,FiniteWilsonTorusGround.block (orbit i) b*
        (FiniteWilsonTorusGround.ground b*scoreAt b) := by
    simpa only [ground,score,mul_assoc] using
      orbit_sum (fun b => FiniteWilsonTorusGround.ground b*scoreAt b) i
  simp_rw [hr]
  norm_num [score,scoreAt,ground,orbit,FiniteWilsonTorusGround.block,Fin.sum_univ_succ]
  rw [normalizer_orbit]
  unfold C
  ring


private def zAt (x : ℝ) : ℝ := ∑ i : Fin 4,
  FiniteWilsonTorusGround.multiplicity i*(FiniteWilsonTorusGround.vectorAt x i)^2

private def cAt (x : ℝ) : ℝ :=
  (3177/2048)*(FiniteWilsonTorusGround.vectorAt x 0)^2-
  2*(225/2048)*FiniteWilsonTorusGround.vectorAt x 0*FiniteWilsonTorusGround.vectorAt x 3+
  (353/18432)*(FiniteWilsonTorusGround.vectorAt x 3)^2

private def residual (x : ℝ) : ℝ :=
  -3243610334169528005827+1953654217580403423644027*x-
  101506400370404313095928928*x^2+452893609599424244451318528*x^3

private theorem residual_positive (x : ℝ) (hx : 2 ≤ x) : 0 < residual x := by
  have h2 : 4 ≤ x^2 := by nlinarith [sq_nonneg (x-2)]
  have h3 : 2*x^2 ≤ x^3 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ x-2) (sq_nonneg x)]
  unfold residual
  nlinarith

private theorem polynomial_reduction (x : ℝ) :
    256*zAt x*cAt x-16*x*zAt x*((FiniteWilsonTorusGround.vectorAt x 0)^2+
      (FiniteWilsonTorusGround.vectorAt x 3)^2)-
      240*x*((FiniteWilsonTorusGround.vectorAt x 0)^2-
        (FiniteWilsonTorusGround.vectorAt x 3)^2)^2 =
    FiniteWilsonTorusGround.polynomial x*((26364470249021444905603896631/65536:ℝ)*x^0 +
      (48324611240374442992181247/256:ℝ)*x^1 +
      (88314023280150270505095/1:ℝ)*x^2 +
      (39917926537471463051008/1:ℝ)*x^3 +
      (15167225843837690118144/1:ℝ)*x^4 +
      (-90196549653161287090176/1:ℝ)*x^5 +
      (410146677799517755015168/1:ℝ)*x^6 +
      (-611965810284577287045120/1:ℝ)*x^7 +
      (518541002330925088899072/1:ℝ)*x^8 +
      (-215162822875748210049024/1:ℝ)*x^9)+
      (73153125/65536)*residual x := by
  norm_num [zAt,cAt,residual,FiniteWilsonTorusGround.vectorAt,
    FiniteWilsonTorusGround.multiplicity,FiniteWilsonTorusGround.polynomial,Fin.sum_univ_succ]
  ring

private theorem scalar_margin : 0 <
    256*Z*C-16*FiniteWilsonTorusGround.value*Z*(FiniteWilsonTorusGround.ground 0^2+
      FiniteWilsonTorusGround.ground 3^2)-
      240*FiniteWilsonTorusGround.value*(FiniteWilsonTorusGround.ground 0^2-
        FiniteWilsonTorusGround.ground 3^2)^2 := by
  have he := polynomial_reduction FiniteWilsonTorusGround.value
  rw [FiniteWilsonTorusGround.value_polynomial,zero_mul,zero_add] at he
  change 256*Z*C-16*FiniteWilsonTorusGround.value*Z*(FiniteWilsonTorusGround.ground 0^2+
      FiniteWilsonTorusGround.ground 3^2)-
      240*FiniteWilsonTorusGround.value*(FiniteWilsonTorusGround.ground 0^2-
        FiniteWilsonTorusGround.ground 3^2)^2=_ at he
  rw [he]
  exact mul_pos (by norm_num) (residual_positive _ FiniteWilsonTorusGround.value_bounds.1)

/-- The ACTUAL centered plaquette-sum lag exceeds its bare1/16 fraction.
This concerns the fixed finite homogeneous torus, not physical4D. -/
theorem centered_score_slowing :
    (1/16:ℝ)*secondMoment (centered score) < lagPairing (centered score) := by
  have he : (16*lagPairing score-secondMoment score-15*(mean score)^2)*
      (FiniteWilsonTorusGround.value*Z^2)=
      256*Z*C-16*FiniteWilsonTorusGround.value*Z*(FiniteWilsonTorusGround.ground 0^2+
        FiniteWilsonTorusGround.ground 3^2)-
        240*FiniteWilsonTorusGround.value*(FiniteWilsonTorusGround.ground 0^2-
          FiniteWilsonTorusGround.ground 3^2)^2 := by
    rw [score_lag,score_second,score_mean]
    field_simp [Z_pos.ne',FiniteWilsonTorusGround.value_pos.ne']
    ring
  have hp : 0 < 16*lagPairing score-secondMoment score-15*(mean score)^2 :=
    (mul_pos_iff_of_pos_right (mul_pos FiniteWilsonTorusGround.value_pos
      (sq_pos_of_pos Z_pos))).mp (by rw [he]; exact scalar_margin)
  rw [centered_second,centered_lag]
  linarith


theorem centered_score_variance_pos : 0 < secondMoment (centered score) := by
  have hex : ∃ i : State, centered score i ≠ 0 := by
    by_cases h : centered score 0=0
    · refine ⟨7,?_⟩
      norm_num [centered,score,scoreAt,orbit] at h ⊢
      linarith
    · exact ⟨0,h⟩
  obtain ⟨i,hi⟩ := hex
  unfold secondMoment
  exact Finset.sum_pos' (fun j _ => mul_nonneg (stationary_positive j).le (sq_nonneg _))
    ⟨i,Finset.mem_univ i,mul_pos (stationary_positive i) (sq_pos_of_ne_zero hi)⟩

private def scoreZ (i : State) : ℤ := (![4,0,0,-4] : Fin 4 → ℤ) (orbit i)

private theorem score_cast (i : State) : (scoreZ i:ℝ)=score i := by
  unfold scoreZ score
  generalize orbit i=b
  fin_cases b <;> norm_num [scoreAt]

private theorem score_integer_eigen (i : State) :
    (∑ j : State,(count (difference i j):ℤ)*scoreZ j)=4096*scoreZ i := by
  fin_cases i <;> decide

theorem bare_score_average (i : State) :
    (∑ j,kinetic i j*score j)=(1/16:ℝ)*score i := by
  have he : (∑ j : State,(count (difference i j):ℝ)*(scoreZ j:ℝ))=
      4096*(scoreZ i:ℝ) := by exact_mod_cast score_integer_eigen i
  simp_rw [score_cast] at he
  unfold kinetic
  simp only [div_mul_eq_mul_div,← Finset.sum_div]
  rw [he]
  ring

theorem bare_score_mean : bareMean score=0 := by
  norm_num [bareMean,score,scoreAt,orbit,Fin.sum_univ_succ]

theorem bare_score_second : bareSecondMoment score=4 := by
  norm_num [bareSecondMoment,score,scoreAt,orbit,Fin.sum_univ_succ]

theorem bare_score_lag : bareLagPairing score=1/4 := by
  have he : (∑ i,score i*(∑ j,kinetic i j*score j))=
      (1/16:ℝ)*(∑ i,score i^2) := by
    simp_rw [bare_score_average]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  unfold bareLagPairing
  rw [he]
  have hs := bare_score_second
  unfold bareSecondMoment at hs
  nlinarith

/-- An observable specified microscopically by elementary plaquettes, centered
separately in the two genuine stationary laws, slows under the spatial weight. -/
theorem plaquette_covariance_increases :
    bareLagPairing score/bareSecondMoment score <
      lagPairing (centered score)/secondMoment (centered score) := by
  rw [bare_score_lag,bare_score_second]
  apply (lt_div_iff₀ centered_score_variance_pos).mpr
  norm_num
  exact centered_score_slowing

end OperatorDerivativeRewrite.Foundation.FiniteWilsonPlaquetteSlowing
