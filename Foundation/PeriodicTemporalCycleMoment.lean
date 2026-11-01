import Foundation.PeriodicIdentitySecondWitness
import Foundation.SU2SharedPlaquetteProjection
/-! Exact reference-Haar winding-cycle contractions for the actual temporal graph.
These are coefficient inputs, not an identification of the full Gibbs law with
independent noise or a completed kernel Taylor expansion. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Topology
namespace OperatorDerivativeRewrite.Foundation.PeriodicTemporalCycleMoment
open QuaternionSU2Representation PeriodicTemporalSlab PeriodicWilsonSlab PeriodicSpatialHolonomy
open SU2WilsonConvolution SU2SharedPlaquetteProjection
attribute [local irreducible] kernel boundaryHaar gaugeHaar spatialAction temporalAction

private theorem pair_contract (L R S : SU2) :
    (∫ X, halfTrace (L*X*R)*halfTrace (S*X⁻¹) ∂law) = halfTrace (R*L*S)/4 := by
  have he : (fun X => halfTrace (L*X*R)*halfTrace (S*X⁻¹)) = sharedProduct (R*L) S := by
    funext X
    have h1 : halfTrace (L*X*R) = halfTrace ((R*L)*X) := by
      rw [halfTrace_mul_comm (L*X) R]
      congr 1
      group
    rw [h1, halfTrace_mul_comm S X⁻¹]
    rfl
  rw [he, sharedProduct_mean]
  rfl

def localProduct (A B C D X Y Z T : SU2) : ℝ :=
  halfTrace (A*Y*X⁻¹)*halfTrace (B*Z*Y⁻¹)*
    halfTrace (C*T*Z⁻¹)*halfTrace (D*X*T⁻¹)

/-- Four coupled links sharing their actual vertex gauge variables contract
with factor1/64. Independent LINK expectations would incorrectly give zero. -/
theorem pinned_cycle_moment (A B C D X : SU2) :
    (∫ Y, ∫ Z, ∫ T, localProduct A B C D X Y Z T ∂law ∂law ∂law) =
      halfTrace (A*B*C*D)/64 := by
  have hT (Y Z : SU2) :
      (∫ T, localProduct A B C D X Y Z T ∂law) =
        halfTrace (A*Y*X⁻¹)*halfTrace (B*Z*Y⁻¹)*
          (halfTrace ((Z⁻¹*C)*(D*X))/4) := by
    have he : (fun T => localProduct A B C D X Y Z T) =
        (fun T => (halfTrace (A*Y*X⁻¹)*halfTrace (B*Z*Y⁻¹))*
          (halfTrace (C*T*Z⁻¹)*halfTrace ((D*X)*T⁻¹))) := by
      funext T
      unfold localProduct
      ring
    rw [he, integral_const_mul, pair_contract]
  simp_rw [hT]
  have hZ (Y : SU2) :
      (∫ Z, halfTrace (A*Y*X⁻¹)*halfTrace (B*Z*Y⁻¹)*
        (halfTrace ((Z⁻¹*C)*(D*X))/4) ∂law) =
        halfTrace (A*Y*X⁻¹)*halfTrace ((Y⁻¹*B)*(C*(D*X)))/16 := by
    have hc (Z : SU2) : halfTrace ((Z⁻¹*C)*(D*X)) = halfTrace ((C*(D*X))*Z⁻¹) := by
      rw [mul_assoc, halfTrace_mul_comm]
    have he : (fun Z => halfTrace (A*Y*X⁻¹)*halfTrace (B*Z*Y⁻¹)*
        (halfTrace ((Z⁻¹*C)*(D*X))/4)) =
        (fun Z => (halfTrace (A*Y*X⁻¹)/4)*
          (halfTrace (B*Z*Y⁻¹)*halfTrace ((C*(D*X))*Z⁻¹))) := by
      funext Z
      rw [hc]
      ring
    rw [he, integral_const_mul, pair_contract]
    ring
  simp_rw [hZ]
  have hc (Y : SU2) : halfTrace ((Y⁻¹*B)*(C*(D*X))) = halfTrace ((B*(C*(D*X)))*Y⁻¹) := by
    rw [mul_assoc, halfTrace_mul_comm]
  have he : (fun Y => halfTrace (A*Y*X⁻¹)*halfTrace ((Y⁻¹*B)*(C*(D*X)))/16) =
      (fun Y => (1/16 : ℝ)*(halfTrace (A*Y*X⁻¹)*halfTrace ((B*(C*(D*X)))*Y⁻¹))) := by
    funext Y
    rw [hc]
    ring
  rw [he, integral_const_mul, pair_contract]
  have hg : (X⁻¹*A)*(B*(C*(D*X))) = X⁻¹*(A*B*C*D)*(X⁻¹)⁻¹ := by group
  rw [hg, halfTrace_conjugate]
  ring

def quadValue (U q : Fin 4 → SU2) : ℝ :=
  localProduct (U 0) (U 1) (U 2) (U 3) (q 0) (q 1) (q 2) (q 3)

theorem quadValue_measurable (U : Fin 4 → SU2) : Measurable (quadValue U) := by
  unfold quadValue localProduct
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul
      all_goals exact halfTrace_measurable.comp (by fun_prop)
    · exact halfTrace_measurable.comp (by fun_prop)
  · exact halfTrace_measurable.comp (by fun_prop)

theorem quadValue_bound (U q : Fin 4 → SU2) : |quadValue U q| ≤ 1 := by
  unfold quadValue localProduct
  rw [abs_mul, abs_mul, abs_mul]
  have h1 : |halfTrace (U 0*q 1*(q 0)⁻¹)| * |halfTrace (U 1*q 2*(q 1)⁻¹)| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul (halfTrace_bound _) (halfTrace_bound _)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  have h2 : |halfTrace (U 0*q 1*(q 0)⁻¹)| * |halfTrace (U 1*q 2*(q 1)⁻¹)| *
      |halfTrace (U 2*q 3*(q 2)⁻¹)| ≤ 1 := by
    simpa only [one_mul] using mul_le_mul h1 (halfTrace_bound _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [one_mul] using mul_le_mul h2 (halfTrace_bound _) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

private theorem cons_measurable {n : ℕ} (A : SU2) :
    Measurable (fun X : Fin n → SU2 => PeriodicWindingEndpointResponse.prepend A X) := by
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.cases ?_ (fun k => ?_) j
  · simpa only [PeriodicWindingEndpointResponse.prepend, Fin.cons_zero] using
      (measurable_const : Measurable (fun _ : Fin n → SU2 => A))
  · simpa only [PeriodicWindingEndpointResponse.prepend, Fin.cons_succ] using
      (measurable_pi_apply k : Measurable (fun X : Fin n → SU2 => X k))

theorem quad_integral (U : Fin 4 → SU2) :
    (∫ q, quadValue U q ∂Measure.pi (fun _ : Fin 4 => law)) = halfTrace (U 0*U 1*U 2*U 3)/64 := by
  have he : (∫ q, quadValue U q ∂Measure.pi (fun _ : Fin 4 => law)) =
      ∫ X, ∫ Y, ∫ Z, ∫ T, localProduct (U 0) (U 1) (U 2) (U 3) X Y Z T ∂law ∂law ∂law ∂law := by
    rw [PeriodicWindingEndpointResponse.head_integral _ 3 _ (quadValue_measurable U) (quadValue_bound U)]
    congr 1
    funext X
    rw [PeriodicWindingEndpointResponse.head_integral _ 2
      (fun q => quadValue U (PeriodicWindingEndpointResponse.prepend X q))
      ((quadValue_measurable U).comp (cons_measurable X)) (fun q => quadValue_bound U _)]
    congr 1
    funext Y
    rw [PeriodicWindingEndpointResponse.head_integral _ 1
      (fun q => quadValue U (PeriodicWindingEndpointResponse.prepend X (PeriodicWindingEndpointResponse.prepend Y q)))
      ((quadValue_measurable U).comp ((cons_measurable X).comp (cons_measurable Y)))
      (fun q => quadValue_bound U _)]
    congr 1
    funext Z
    rw [PeriodicWindingEndpointResponse.head_integral _ 0
      (fun q => quadValue U (PeriodicWindingEndpointResponse.prepend X
        (PeriodicWindingEndpointResponse.prepend Y (PeriodicWindingEndpointResponse.prepend Z q))))
      ((quadValue_measurable U).comp ((cons_measurable X).comp
        ((cons_measurable Y).comp (cons_measurable Z)))) (fun q => quadValue_bound U _)]
    congr 1
    funext T
    change (∫ _ : Fin 0 → SU2, localProduct (U 0) (U 1) (U 2) (U 3) X Y Z T
      ∂Measure.pi (fun _ : Fin 0 => law)) = _
    simp only [integral_const, probReal_univ, one_smul]
  rw [he]
  simp_rw [pinned_cycle_moment]
  simp only [integral_const, probReal_univ, one_smul]

abbrev Row := Fin 2 → ZMod 4
def vertex (r : Row) (j : Fin 4) : SpatialVertex := ![r 0, (j.val : ZMod 4), r 1]
def edge (r : Row) (j : Fin 4) : SpatialEdge := (vertex r j, 1)
def select (r : Row) (a : Gauge) (j : Fin 4) : SU2 := a (vertex r j)

private theorem vertex_injective : ∀ r : Row, Function.Injective (vertex r) := by decide
private theorem vertex_shift : ∀ (r : Row) (j : Fin 4), shift (vertex r j) 1 = vertex r (j+1) := by decide

private theorem winding_product (U : State) (r : Row) :
    winding U (vertex r 0) 1 = U (edge r 0)*U (edge r 1)*U (edge r 2)*U (edge r 3) := by
  simp only [winding, thrice, twice, vertex_shift]
  rfl

/-- An actual four-vertex marginal of the full64-vertex gauge Haar law. This
does not assert independence under a nonzero-coupling Gibbs law. -/
theorem select_preserving (r : Row) :
    MeasurePreserving (select r) gaugeHaar (Measure.pi (fun _ : Fin 4 => law)) := by
  unfold gaugeHaar select
  have hi := iIndepFun_pi (μ := fun _ : SpatialVertex => law) (X := fun _ => id)
    (fun _ => aemeasurable_id)
  have hs := hi.precomp (vertex_injective r)
  have hm := hs.map_fun_eq_pi_map (fun j => (measurable_pi_apply (vertex r j)).aemeasurable)
  simp only [(measurePreserving_eval (fun _ : SpatialVertex => law) _).map_eq] at hm
  exact ⟨measurable_pi_iff.mpr (fun _ => measurable_pi_apply _), hm⟩

def temporalProduct (U V : State) (r : Row) (a : Gauge) : ℝ :=
  halfTrace (temporalWord U V a (edge r 0))*halfTrace (temporalWord U V a (edge r 1))*
    halfTrace (temporalWord U V a (edge r 2))*halfTrace (temporalWord U V a (edge r 3))

private theorem actual_value (U : State) (r : Row) (a : Gauge) :
    temporalProduct U 1 r a = quadValue (fun j => U (edge r j)) (select r a) := by
  unfold temporalProduct quadValue localProduct temporalWord select edge
  simp only [Pi.one_apply, inv_one, mul_one, vertex_shift]
  rfl

/-- Full reference-Haar integral of four ACTUAL coupled temporal traces on
one periodic winding row, including all other60 gauge vertices. -/
theorem actual_winding_moment (U : State) (r : Row) :
    (∫ a, temporalProduct U 1 r a ∂gaugeHaar) =
      halfTrace (winding U (vertex r 0) 1)/64 := by
  have hm := select_preserving r
  have hh := integral_map (μ := gaugeHaar) hm.measurable.aemeasurable
    (quadValue_measurable (fun j => U (edge r j))).aestronglyMeasurable
  rw [hm.map_eq] at hh
  change (∫ q, quadValue (fun j => U (edge r j)) q ∂Measure.pi (fun _ : Fin 4 => law)) =
    ∫ a, quadValue (fun j => U (edge r j)) (select r a) ∂gaugeHaar at hh
  simp_rw [actual_value]
  rw [← hh, quad_integral]
  rw [winding_product]

private theorem flip_product (U : State) (r : Row) (a : Gauge) :
    temporalProduct U (PeriodicCenterSeam.flip 1 1) r a =
      temporalProduct (PeriodicCenterSeam.flip 1 U) 1 r a := by
  have hw (e : SpatialEdge) : temporalWord U (PeriodicCenterSeam.flip 1 1) a e =
      temporalWord (PeriodicCenterSeam.flip 1 U) 1 a e := by
    have hh := PeriodicCenterSeam.temporal_word 1 (PeriodicCenterSeam.flip 1 U) 1 a e
    rw [PeriodicCenterSeam.flip_involutive] at hh
    exact hh
  unfold temporalProduct
  simp_rw [hw]

/-- A center seam changes the sign of this winding product EXACTLY once.
No Taylor truncation or Gaussian product law is used. -/
theorem twisted_value (U : State) (r : Row) (a : Gauge) :
    temporalProduct U (PeriodicCenterSeam.flip 1 1) r a = -temporalProduct U 1 r a := by
  have hn0 : (0 : ZMod 4) ≠ 3 := by decide
  have hn1 : (1 : ZMod 4) ≠ 3 := by decide
  have hn2 : (2 : ZMod 4) ≠ 3 := by decide
  have h0 : (PeriodicCenterSeam.flip 1 U) (edge r 0) = U (edge r 0) := by
    simp [PeriodicCenterSeam.flip, PeriodicCenterSeam.seam, edge, vertex, hn0]
  have h1 : (PeriodicCenterSeam.flip 1 U) (edge r 1) = U (edge r 1) := by
    simp [PeriodicCenterSeam.flip, PeriodicCenterSeam.seam, edge, vertex, hn1]
  have h2 : (PeriodicCenterSeam.flip 1 U) (edge r 2) = U (edge r 2) := by
    simp [PeriodicCenterSeam.flip, PeriodicCenterSeam.seam, edge, vertex, hn2]
  have h3 : (PeriodicCenterSeam.flip 1 U) (edge r 3) = SU2StapleExtremes.minusOne * U (edge r 3) := by
    simp [PeriodicCenterSeam.flip, PeriodicCenterSeam.seam, edge, vertex]
  rw [flip_product, actual_value, actual_value]
  dsimp only [quadValue, localProduct]
  rw [h0, h1, h2, h3]
  have hg : (SU2StapleExtremes.minusOne * U (edge r 3)) * select r a 0 * (select r a 3)⁻¹ =
      SU2StapleExtremes.minusOne * (U (edge r 3) * select r a 0 * (select r a 3)⁻¹) := by group
  rw [hg, SU2StrongCouplingCovariance.halfTrace_center_neg]
  ring

theorem twisted_winding_moment (U : State) (r : Row) :
    (∫ a, temporalProduct U (PeriodicCenterSeam.flip 1 1) r a ∂gaugeHaar) =
      -halfTrace (winding U (vertex r 0) 1)/64 := by
  simp_rw [twisted_value]
  rw [integral_neg, actual_winding_moment]
  ring

def orbit (h : ℝ) : State := PeriodicEndpointScore.left h PeriodicEndpointFibreWitness.leftEndpoint

private theorem orbit_edge (h : ℝ) (r : Row) (j : Fin 4) :
    orbit h (edge r j) = SU2JointPlaquetteCubic.axis 0 h := by
  have hn : edge r j ≠ PeriodicCancellingBoundaryResponse.edge := by
    intro hh
    have hd := congrArg Prod.snd hh
    change (1 : Fin 3) = 0 at hd
    exact (by decide : (1 : Fin 3) ≠ 0) hd
  unfold orbit PeriodicEndpointScore.left PeriodicEndpointFibreWitness.leftEndpoint
  simp only [Function.update, dite_eq_right hn, Pi.one_apply, mul_one]

theorem orbit_winding (h : ℝ) (r : Row) : halfTrace (winding (orbit h) (vertex r 0) 1) = Real.cos (4*h) := by
  rw [winding_product]
  rw [orbit_edge, orbit_edge, orbit_edge, orbit_edge]
  simp only [PeriodicWindingEndpointResponse.axis_add]
  rw [show h+h+h+h=4*h by ring, FourCubeWilsonCubic.axis_trace]

def rowDifference (h : ℝ) (r : Row) : ℝ :=
  (∫ a, temporalProduct (orbit h) 1 r a ∂gaugeHaar) -
    ∫ a, temporalProduct (orbit h) (PeriodicCenterSeam.flip 1 1) r a ∂gaugeHaar

theorem row_difference (h : ℝ) (r : Row) : rowDifference h r = Real.cos (4*h)/32 := by
  rw [rowDifference, actual_winding_moment, twisted_winding_moment, orbit_winding]
  ring

def windingSector (h : ℝ) : ℝ := ∑ r : Row, rowDifference h r

/-- The exact sixteen-row winding contribution. Identification with the FULL
fourth-order kernel coefficient still requires eliminating all other edge tuples. -/
theorem winding_sector (h : ℝ) : windingSector h = Real.cos (4*h)/2 := by
  have hc : Fintype.card Row = 16 := by simp [Row]
  unfold windingSector
  simp_rw [row_difference]
  rw [Finset.sum_const, Finset.card_univ, hc, nsmul_eq_mul]
  norm_num
  ring

theorem winding_sector_second : HasDerivAt (deriv windingSector) (-8) 0 := by
  have he : windingSector = (fun h : ℝ => Real.cos (4*h)/2) := funext winding_sector
  rw [he]
  have hd : deriv (fun h : ℝ => Real.cos (4*h)/2) = (fun h : ℝ => -2*Real.sin (4*h)) := by
    funext h
    have hh := ((hasDerivAt_id h).const_mul 4).cos.div_const 2
    simp only [id_eq] at hh
    convert hh.deriv using 1 <;> ring
  rw [hd]
  convert (((hasDerivAt_id (0 : ℝ)).const_mul 4).sin).const_mul (-2) using 1 <;> norm_num

end OperatorDerivativeRewrite.Foundation.PeriodicTemporalCycleMoment
