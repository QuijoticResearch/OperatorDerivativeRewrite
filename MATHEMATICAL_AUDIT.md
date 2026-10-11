# Mathematical audit: L² multiplication

## Scope and verification status

This audit concerns `C:/Operator/OperatorDerivative.lean` and
`C:/Operator/OperatorDerivative.tex`. Line numbers below refer to those unchanged originals.
The abstract energy-space interfaces have **not** been rewritten or imported into the new
foundation. Their conditional algebraic proofs do not establish that their fields admit
pointwise interpretations on an arbitrary probability space.

The new `Foundation/LpProducts.lean` uses Mathlib's `MemLp`, `Lp`, `HolderTriple`,
`MemLp.of_bilin`, Hölder estimates, and the concrete `L2.inner_def`.
The original monolith is not claimed to compile or to have an axiom-free verification.
The counterexample and proposed operator-domain arguments below are mathematical analysis;
they are not claimed as Lean theorems of this increment.

## A precise probability-space counterexample

Let Ω = (0,1), with its Borel sigma-algebra and restricted Lebesgue measure P.
This is a probability space. Set f(x) = g(x) = x^(-1/3). Then

- ∫ |f|² dP = ∫₀¹ x^(-2/3) dx = 3, and likewise for g, so f,g ∈ L².
- fg = x^(-2/3) lies in L¹, with integral 3.
- ∫ |fg|² dP = ∫₀¹ x^(-4/3) dx = ∞, so fg ∉ L².

Consequently a total L² × L² → L² operation agreeing a.e. with pointwise
multiplication cannot exist on this space. Taking H = ℝ and u = v = f also
refutes total L² scalar–vector multiplication into L² and total pointwise
inner products of L² vectors into L². Any proposed L² representative would
have the same infinite squared integral by a.e. equality.

L² multiplication also lacks the continuity needed for an L² density extension:
f_n = n^(1/2) 1_(0,1/n²) has ‖f_n‖₂ = n^(-1/2) → 0 but ‖f_n²‖₂ = 1.
Thus a continuous bilinear L²-valued extension cannot supply the missing operation.

## Correct integrability and estimates

For 1/r = 1/p + 1/q (including 1/∞ = 0), Hölder and pointwise
Cauchy–Schwarz give, for a real inner-product space H,

    ‖fg‖_r ≤ ‖f‖_p ‖g‖_q
    ‖fu‖_r ≤ ‖f‖_p ‖u‖_q
    ‖⟨u,v⟩_H‖_r ≤ ‖u‖_p ‖v‖_q.

Membership includes a.e. strong measurability. These statements hold on arbitrary
measure spaces; finiteness or probability is unnecessary for the product estimates.

| Inputs | Output, for all three operations | Intended use |
| --- | --- | --- |
| L², L² | L¹ | Scalar or vector pairings and their expectations |
| L⁴, L⁴ | L² | Products and derivative terms in a D^{1,4} product argument |
| L∞, L² | L² | Bounded multipliers on the Hilbert energy space |
| L∞, L¹ | L¹ | Bounded weights on pointwise pairings |
| L⁸, L⁸ | L⁴ | Intermediate products when another L⁴ operation is required |

The actual L² Hilbert inner product is ∫ ⟨u(ω),v(ω)⟩_H dP, with an L¹
integrand, and its absolute value is at most ‖u‖₂‖v‖₂.
The random variable ⟨u,v⟩ is L² precisely when its square is integrable
(with measurability); a sufficient condition is u,v ∈ L⁴. The stronger
condition ‖u‖‖v‖ ∈ L² is sufficient but not necessary because of cancellation
or pointwise orthogonality. Similarly, scalar fu is L² precisely when
|f|‖u‖ ∈ L², with the appropriate measurability.
On a probability space L⁴ ⊂ L² and L² ⊂ L¹, but neither inclusion reverses.
Constants act on L² through a fixed bounded linear map, without an L⁴ assumption.

## Incorrect structure fields and their locations

The following is the complete field inventory of the three original product interfaces.
Algebraic identities are pointwise valid; the defect is their total L² typing.
Constant-only special cases are separately preservable.

| Interface and original lines | Fields | Correction |
| --- | --- | --- |
| `UnboundedEnergySpace`, 137–141 | `mul`, `smul`, `pip` | Replace total L² outputs by exponent-indexed operations or restricted L² products |
| Same, 143–153 | `inner_eq_expect_pip`, `pip_smul`, `pip_symm`, `smul_selfadj`, `smul_add_left`, `smul_mul_assoc`, `smul_add_right`, `smul_finset_sum` | Integrate L¹ pairings; restrict multipliers; type each intermediate product with its actual exponent |
| Same, 155–156 | `mul_dom` | dom(D) × dom(D) closure is not automatic; D^{1,4} requires BOTH values and derivatives in L⁴ and a proved approximation argument |
| Same, 161–165 | `inner_eq_expect_mul`, `mul_comm`, `mul_assoc`, `mul_sub` | Pairing in L¹; products and identities with compatible exponents |
| `EnergySpace`, 748–754 | `mul`, `smul`, `pip`, `inner_eq_expect_mul`, `inner_eq_expect_pip` | Same typing correction; boundedness of D does not repair multiplication |
| Same, 758, 766–773 | `mul_const_centered`, `mul_comm`, `mul_assoc`, `mul_add`, `mul_sub`, `mul_constEmb`, `pip_smul`, `pip_symm`, `smul_selfadj` | Constant multipliers are valid; general identities need restricted types and integrable pairings |
| Same, 777–789 | `smul_add_left`, `smul_mul_assoc`, `smul_add_right`, `smul_finset_sum`, `pip_finset_sum_left` | Preserve algebra only after giving the terms correct spaces |
| `ConcreteEnergyData`, 2810–2812 | `mul`, `smul`, `pip` | Despite using concrete Mathlib Lp types, the outputs remain incorrect |
| Same, 2824–2835 | `inner_eq_expect_pip`, `pip_smul`, `pip_symm`, `smul_selfadj`, `smul_add_left`, `smul_mul_assoc`, `smul_add_right`, `smul_finset_sum` | Same restricted operations and L¹ expectations |
| Same, 2836–2839, 2842–2845 | `mul_dom`, `inner_eq_expect_mul`, `mul_comm`, `mul_assoc`, `mul_sub` | Same domain and exponent corrections |
| `UnboundedCylindricalStructure`, 354–373 | `mul_cyl`, `coord_leibniz`, `ibp_formula`, `leibniz_closure` | Specify integrability of cylindrical values, coordinate derivatives and random representers; prove closure in the L⁴ graph topology |
| `CylindricalStructure`, 1437–1452 | Same four fields | Extending to all L² is invalid even if D is bounded; use a restricted core |
| `UnboundedSmoothFunc`, 493–497 | `chain_rule`, `chain_rule_deriv` | Prove composition/domain results; bounded φ',φ'' are sufficient for the scalar actions but do not prove a chain rule |
| `UnboundedStochVolAssumption`, 549–556 | `inv_σ`, `brown_leibniz`, `transfer_formula` | An L² reciprocal is not a multiplier on all L²; require a bounded reciprocal or individual product/weighted-domain membership |

`expect` on L² is not itself incorrect on a probability space. The error is using it
as though every random product were in L²; define the integral/expectation on L¹ instead.
`expect_smul` and constant embeddings do not assume general product closure.

## Affected declarations and downstream consequences

Each row identifies every direct use of the erroneous abstract operations in declarations
or proofs, together with the associated wrappers. A conditional theorem in the old abstract
interface may have a valid algebraic proof, but does not establish a theorem for concrete L².

| Original declarations (start lines) | Original claim / required correction |
| --- | --- |
| `LeibnizCondition_unbounded` 335; `ibp_rep_unbounded` 378; `cylindrical_leibniz_unbounded` 392; `cylindrical_implies_leibniz_unbounded` 407; `malliavin_deriv_unbounded` 412; `D_eq_malliavin_unbounded` 416 | Total products appear before domain hypotheses. Use a core with actual multiplier/derivative membership; membership in dom(D) alone is insufficient |
| `ProductRule_unbounded` 423; `leibniz_implies_product_rule_unbounded` 433 | hFu proves only divergence-domain membership of an already typed product. It does not justify Fδu or ⟨DF,u⟩ ∈ L². Require those separately, or sufficient L∞/L⁴ conditions |
| `intrinsic_bracket_unbounded` 500; `ito_correction_unbounded` 504; `ito_correction_from_product_rule_unbounded` 508; `operator_ito_decomposition_unbounded` 520 | Bracket is naturally L¹. Bounded φ'' times bracket is still only L¹. An L² equation needs additional bracket/cross-pairing integrability |
| `leibniz_stochastic_volatility_unbounded` 560; `transfer_preserves_pip` 581; `gubinelli_base_invariance` 595; `main_pipeline` 672 | Reciprocal-volatility products and nested cross-products need their own exponents or restricted weighted domains; algebra alone proves no integrability |
| `adjoint_prob` 806; `D_const` 817; `mul_pip_eq_pip_smul` 841; `const_perp_Im_delta` 991; `PRP_from_ker_D_subset_constants` 1032 | Adjoint/constant/representation reasoning can use Hilbert pairings directly. `mul_pip_eq_pip_smul` is a triple-product identity, not an unrestricted L² identity |
| `LeibnizCondition` 1126; `ProductRule` 1129; `leibniz_iff_product_rule` 1133 | Statements quantify over all L² inputs with false product typing. Reformulate on a proved test core and multiplier domains; no automatic equivalence on all L² |
| `chain_rule_sq` 1218; `pow'` 1224; `chain_rule_pow` 1229 | Squaring needs F ∈ L⁴ to yield L²; an nth power needs F ∈ L^{2n}. Derivative terms F^{n-1}DF need their own L² membership |
| `chain_rule_defect` 1341; `chain_rule_from_density` 1357; `leibniz_defect` 1421 | Defects are not everywhere defined on L². Need composition estimates or L⁴ value-and-derivative convergence, not only L² density/closedness |
| `ibp_rep` 1455; `cylindrical_leibniz_on_class` 1468; `cylindrical_implies_leibniz` 1482 | Coordinate derivative times representer is L² for deterministic representers or bounded coefficients; two arbitrary L² factors only give L¹ |
| `RepresentersDeterministic` 1496; `representer_rigidity` 1515; `deterministic_variance_bound` 1537 | Triple products need integrability. A deterministic κ does NOT imply expectation factorization against arbitrary random u; that is an additional, generally false assumption |
| `RepresentersNondegenerate` 1562; `stoch_vol_representers` 1569; `stoch_vol_pip` 1575; `stoch_vol_obstruction` 1590 | Nondegeneracy can be pointwise/L¹; transferred representers need restricted products. hcancel is independently false: on (0,1), F=1+x, G=1/(1+x) are bounded, F nonconstant and FG=1 with G≠0 |
| `GaussianVolterra` 1649; `leibniz_gaussian` 1659; `leibniz_fBM` 1830; `full_calculus_fBM` 1836 | Inherit/propagate the invalid universal Leibniz interface; Gaussian moments of coordinates do not apply to every L² functional |
| `gubinelli_derivative` 1689; `rough_path_lift` 1724; `is_controlled` 1731; `gubinelli_remainder` 1740; `controlled_pythagoras` 1751 | Products defining lifts, remainders and ratios/cross-products require L² membership. Pythagoras is valid once those elements exist and orthogonality is established |
| `EnergySpace.intrinsic_bracket` 1996; `EnergySpace.ito_correction` 2001; `ito_formula_bounded` 2021; `ito_formula_with_clark_ocone` 2046 | Brackets/corrections default to L¹; boundedness of δ/D or φ'' does not upgrade them to L². Projection commutation with a random multiplier is a separate hypothesis |
| `ItoProcess.bracket` 2098; `ito_formula_time_indexed` 2118; `ito_formula_integrated` 2141; `ito_from_leibniz_alone` 2207 | In addition to pointwise L² correction requirements, integrated statements need time-integrability and divergence-domain facts; these are not supplied by Hölder alone |
| `EnergySpace.numberOperator_selfadj` 2491 | Proof uses the probabilistic bridge; preserve the substantive operator theorem using adjointness directly |
| `EnergySpace.covariance` 2568; `EnergySpace.covariance_eq_inner_centered` 2572; `EnergySpace.covariance_symm` 2594; `EnergySpace.variance` 2600; `EnergySpace.ito_isometry_concrete` 2605 | Centered covariance/variance integrands are L¹. The real-valued formulas survive without a total L² multiplication operation |
| `ConcreteEnergyData.toUnboundedEnergySpace` 2856 | Forwards the bad fields; not a construction of admissible pointwise operations |
| `brownianEnergySpace` 3466, especially parameters 3475–3487 | Assumes total mul/smul/pip AND agreement a.e. Their existence is false on general probability spaces; proving algebra from these hypotheses does not construct Brownian energy data |

Representation, projection and pure adjoint results that merely inherit an energy-space
parameter need a later separation from the product interface. No integrability correction
is required for their Hilbert-space inner products themselves. The stochastic Fubini
lemmas 1944/1955 use bounded linear maps and Bochner integrability, not L² product closure.

## Correct concrete fragments to preserve

- `L2_inner_eq_integral` 2707, `L2H_inner_eq_integral` 2725,
  `L2_smul_const` 2996 and its algebra/inner-product lemmas 3020, 3738–3768, 4273:
  Hilbert pairings and multiplication by a fixed deterministic vector are correctly typed.
- `ibp_algebraic_step` 3054, `inner_eq_expect_mul_concrete` 3245:
  integrate L² pairings in L¹ rather than package them as L² products.
- `concrete_mul` 3274 and `concrete_mul_comm` 3279 already use L⁴ × L⁴ → L².
- `pip_memLp_one` 3297, `concrete_pip_L1` 3305,
  `inner_eq_expect_pip_concrete` 3312 correctly give L¹ vector pairings.
- `concrete_mul_assoc` 3337, `concrete_mul_add` 3350, `concrete_mul_const` 3359,
  `concrete_pip_smul` 3369, `concrete_pip_symm` 3381, `concrete_smul_selfadj` 3392
  are pointwise identities. They do not establish integrability of their expressions.
  The extra L⁴ membership assumptions in the pointwise associativity lemma are unused;
  quotient-valued iterated products need appropriate intermediate membership.
- `isonormal_memLp_any` 3650 and `isonormal_memLp_four` 3673 concern Gaussian
  coordinates, not arbitrary elements of dom(D). `memLp_four_mul_of_memLp_eight` 3683
  is a correctly restricted Hölder claim.
- `memLp_two_of_memLp_four` 4427, `memLp_two_mul_of_memLp_four` 4452,
  `Lp4_mul` 4460, `Lp4_mul_comm` 4468, `memLp_four_const` 4479,
  `memLp_two_const_mul` 4485, `L4_inner_mul_well_defined` 4492 have correct
  mathematical integrability types. Finite measure is unnecessary for the product
  itself, but necessary for the inclusion L⁴ ⊂ L²; constants need finite measure.
- Concrete covariance identities 4293–4305 and finite-sum cylindrical derivative
  pairings 4321 are compatible with L¹ expectations.
- `ito_adjoint_level1` 4781, `ito_adjoint_level2` 4817,
  `ito_correction_concrete` 4839 express conditional integral pairings, not universal
  L² closure. They still require their declared Stein assumptions.
- `cylindrical_compose` 4892 and `cylindrical_chain_rule` 4920 explicitly assume
  membership of each derivative product; those hypotheses must be established for
  any eventual application, and are not themselves integrability proofs.
- `bilinear_identity_extends_by_density` 4962 is valid for actual continuous bilinear
  maps; it cannot be applied to the nonexistent L²-valued pointwise product.
  `complete_stochastic_calculus` 5132 packages conditional results including a
  correctly restricted L⁴ product; it does not repair the energy-space interfaces.

## Manuscript and comments requiring correction

| Original location | Claim / consequence |
| --- | --- |
| Lean 155, 2836, 3632–3649 | dom(D) is described as D^{1,4}, or as contained in L⁴, without value AND derivative L⁴ estimates. Linear Gaussian coordinates have moments; general Sobolev functionals need not have all moments |
| Lean `cylindrical_memLp_four` 3704 | The L⁴ conclusion is exactly the hpoly hypothesis. This proves no new polynomial-growth estimate. General smooth functions can grow too quickly |
| TeX 739 | D^{1,4} = D^{1,2} ∩ L⁴ is asserted via Meyer inequalities. L⁴ values alone do not supply L⁴ derivatives; retain the definition requiring both and prove any special implication separately |
| TeX 810 | Two L² norm factors claimed to have L² product by Cauchy–Schwarz. Correct output is L¹; use both L⁴, one L∞, or an independently proved squared-product integrability condition |
| TeX 674, 711–727 | Restricted-core and L⁴ graph-convergence approach is the right direction. Stability, density, derivative identification and estimates still need proofs; this is not all-dom(D) closure |
| TeX 783–805 | Product rule hypotheses correctly include F bounded and ‖DF‖‖u‖ ∈ L², but extension from bounded tests requires a graph core for D, not just L² density. Identifying D* with δ requires δ closed (or uses its closure) |
| TeX 108–112, 777 onward | An L² Itô correction/bracket requires fourth moments or another proved L² bound; L² regularity of DY alone only gives an L¹ bracket |
| Lean 3419–3448 | L⁴→L² multiplication, deterministic-vector multiplication and L¹ pip cannot fill the old total L² fields. They have different domains/codomains |

## Proposed interface, for a later increment

1. Keep the operator layer separate: X = Lp ℝ 2 P, V = Lp H 2 P,
   a densely defined δ : V →ₗ.[ℝ] X, and D = δ*. Keep Hilbert pairings native.
2. Use `lpMul`, `lpSmul`, `lpInner` with explicit Hölder exponents. Expectation is
   the integral of an L¹ scalar random variable. General pointwise pairings land
   in L¹; real constants remain ordinary scalar actions.
3. Multipliers on all of X or V come from Lp ℝ ∞ P. For more general random
   multipliers use the restricted domain {u ∈ V : fu ∈ L²}; prove membership for
   each application. Do not extend a product by zero outside this domain.
4. Define a D^{1,4} candidate as F ∈ dom(D) with F ∈ L⁴ AND DF ∈ L⁴(H), using
   a.e.-compatible Lp representatives. This is not automatically an algebra:
   Hölder only puts FG and F DG + G DF in L². A core approximation and closedness
   of D are needed to prove FG ∈ dom(D) and identify its derivative.
5. For the divergence product rule use F ∈ dom(D) ∩ L∞, u ∈ dom(δ), and
   ⟨DF,u⟩ ∈ L² (sufficient: DF,u ∈ L⁴, or ‖DF‖‖u‖ ∈ L²).
   Then Fu and Fδu are L² by the bounded-multiplier estimate. To PROVE Fu ∈ dom(δ)
   via adjointness, prove the identity on a graph-dense core of dom(D), with
   multiplication/Leibniz compatibility there, extend it to all dom(D), and use
   δ = D* only after proving δ closed. If δ is merely closable, the conclusion
   concerns its closure. No such domain theorem is implemented in this increment.
6. Treat brackets as L¹ by default. Add explicit L⁴ estimates on ΠDY or direct
   squared-pairing estimates before any L² correction theorem. An orthogonal
   projection on L² need not be bounded on L⁴ or commute with random multiplication.
7. In weighted stochastic-volatility energy spaces, division by σ may be a
   weighted isometry even if 1/σ is unbounded. Construct those spaces/maps and their
   restricted domains; do not model division as unrestricted L² multiplication.

Unresolved mathematical questions: what concrete δ and core are intended; is δ closed;
which cylindrical approximations converge in the L⁴ graph norm; which projection has
L⁴ estimates; which bracket/time-integrability bounds hold; and whether the intended
bounded predictable adjoint or unbounded Malliavin adjoint has the desired Leibniz rule.
Integrability is necessary for these statements but does not prove any of those identities.

## Lean declarations established in this increment

Namespace: `OperatorDerivativeRewrite.Foundation`.

- `holderTripleFourFourTwo` proves the exponent arithmetic, not an axiom.
- `mul_memLp`, `smul_memLp`, `inner_memLp`: membership at exponent r for
  `HolderTriple p q r` and actual `MemLp` inputs.
- `mul_eLpNorm_le`, `smul_eLpNorm_le`, `inner_eLpNorm_le`: the three Hölder
  seminorm estimates at the same exponents.
- `lpMul`, `lpSmul`, `lpInner`: constructions on Mathlib Lp equivalence classes.
  The three `_coeFn` theorems prove agreement a.e. with pointwise operations;
  the three `_norm_le` theorems prove the corresponding real-valued Lp norm bounds.
- `mul_L2_integrable`, `inner_L2_integrable`, `smul_L2_memLp_one` establish the
  L² × L² → L¹ cases (scalar/vector pairings Bochner-integrable where stated).
- `mul_L4_memLp_two`, `smul_L4_memLp_two`, `inner_L4_memLp_two` establish
  L⁴ × L⁴ → L²; the three `*_Linfty_L2_memLp_two` establish L∞ × L² → L².
- `L2_inner_eq_integral`, `L2_integral_inner_bound` identify and bound the
  integrated vector pairing.
- `L2_bounded_multiplier_selfadj` proves symmetry of multiplication by a real
  L∞ element on L²(H). It does not identify the multiplier with an operator adjoint
  through a newly constructed continuous-linear-map interface.

Verification: `lake build` and `lake build Foundation.AxiomAudit` succeed with pinned
Lean/Mathlib v4.34.1. `#print axioms` is included for **every** new declaration.
All report only `propext`, `Classical.choice`, `Quot.sound`; none depend on `sorryAx`
or a custom axiom. Existing unused-section-variable warnings in `Adjoint.lean` remain.

## Domain reconstruction milestone (after db345dc)

### Original domain and closure inventory

| Original location | Actual Lean content | Mathematical assessment / repair |
| --- | --- | --- |
| Lean 62–80 | D = δ.adjoint, closedness and adjoint identity under dense δ-domain | Preserve; this is the actual operator and domain used in the new modules |
| Lean `UnboundedEnergySpace` 101–170, especially 110–113 | δ is a LinearPMap and δ.domain is dense; comment calls δ closable | No `IsClosable` field is present. Density gives an adjoint and closedness, but alone does not imply density of its domain |
| Lean 130, 167–170 | Proj sends every vector into dom(δ); dom(D) is dense; dense pairing nondegeneracy | These are extra analytic hypotheses, not consequences of δ-density. Projection-domain invariance needs a concrete proof; D-density needs closability of δ or a separate proof |
| Lean 155–156, 2836–2839 | `mul_dom` asserts product closure for every pair in dom(D) | Invalid as a consequence of closedness. Remove this universal closure; replace it with a proved restricted-core result |
| Lean 180–187 | U.D = U.δ.adjoint and its domain-specific identity | Preserve. Membership must refer to this adjoint, not a newly assigned derivative |
| Lean 201–208, 226, 289, 314 | PRP/isometry and factorization/orthogonality/variance with explicit δ/D domain elements and projection-domain hypotheses | Those hypotheses remain needed. They are independent of multiplication closure |
| Lean `LeibnizCondition_unbounded` 335–338 | Identity for F,G in dom(D), with separate hFG, but total L² products | hFG is logically separate, but the ambient products are already incorrectly typed. Use restricted products; do not infer hFG from closedness |
| Lean `UnboundedCylindricalStructure` 341–373 | `cyl_in_dom`, `mul_cyl`, `coord_leibniz`, `ibp_formula`; `cyl_dense` merely supplies a sequence of cylindrical elements; `leibniz_closure` assumes the extension | No smoothness or derivative relation is encoded for coordinate derivatives. There is NO convergence clause in `cyl_dense`. Neither density nor the extension is proved by these fields |
| Lean 378–416 | IBP identification and cylindrical/global Leibniz wrappers | Formal algebra under supplied hypotheses. A real coordinate derivative and verified IBP are required for mathematical identification |
| Lean `ProductRule_unbounded` 423–476 | Divergence identity requires hFu, and proof uses universal `mul_dom` | Replace with bounded/restricted multipliers, correct L² pairings and separate domain facts. The present multiplier criterion supplies a sufficient δ-domain condition, but does not identify the commutator as contraction with DF |
| Lean `UnboundedSmoothFunc` 484–497 | `app_in_dom`, `deriv1_in_dom`, two chain rules assumed | Composition-domain membership and chain identities must be separately proved for a genuine scalar function; smoothness is not encoded here |
| Lean 546–560, 672 | Reciprocal volatility and Brownian derivative transfer and Leibniz assumptions | Require an actual Brownian derivative domain and a proved weighted transfer. Scalar L² reciprocity is not an everywhere-defined multiplier |
| Lean `EnergySpace` 735–799 | δ is continuous and everywhere defined; D is its continuous adjoint | Both domains really are the whole Hilbert spaces. This does not make L² an algebra or make D a derivation |
| Lean 1126–1204 | Universal bounded `LeibnizCondition`, `ProductRule`, equivalence | Universal pointwise L² typing fails. Even on a bounded test algebra, Leibniz requires separate structure on the actual adjoint |
| Lean 1218–1411 | Powers and chain-rule approximation/continuity assumptions | Use actual bounded test products or verified moment bounds. The hypotheses called polynomial approximation do not encode polynomials. Defect continuity cannot be assumed to establish a nonexistent L² product |
| Lean `CylindricalStructure` 1429–1452 and wrappers 1455–1484 | Assumed algebraic class and IBP; `leibniz_closure` concludes Leibniz on all L² | Separate algebraic closure, actual operator membership, actual derivative identity, and the topology of extension |
| Lean 1649–1661, 1830–1841 | Gaussian/fBM structures carry or propagate the previous closure assumptions | Gaussian marginals do not supply graph density or closure of dom(D) |
| Lean `ConcreteStochasticIntegral` 2768–2788 | Dense δ-domain, centeredness and exact isometry on its entire domain | Isometry makes δ bounded on that domain and gives a bounded extension. If also closed, its dense domain must be the whole space. This is not a generic unbounded Skorokhod divergence interface |
| Lean `ConcreteEnergyData` 2806–2850 and converter 2856 | Repeats universal `mul_dom`, D-density and projection-domain assumptions | Concrete Lp types do not prove these assumptions. Use the new primitive domain statements before assembling another energy interface |
| Lean `CylindricalFunctional` 2939–2967 | Separate `f_eval`, `df_eval`, F and dF, with a.e. evaluation specifications | No `ContDiff` or derivative relation ties df_eval to f_eval; no membership of F in the actual δ* domain. Do not reuse this as a verified cylindrical derivative |
| Lean 3632–3724, 4427–4492 | Intended Sobolev/core closure comments and correct Lp product facts | L⁴ product estimates are useful, but neither identify dom(D) with D^{1,4} nor prove domain closure. `cylindrical_memLp_four` returns its own membership hypothesis |
| Lean 4712–4748, 4892–4937 | Smooth/composed cylindrical packages and formula unfolding | Some scalar derivative hypotheses are supplied, but actual δ*-domain identification and representation independence remain separate tasks |
| Lean 4943–4999 | Continuous-bilinear density theorem and commented-out domain extension | The generic theorem is valid. It does not construct a graph space or prove continuity of a defect that uses D(FG) before product-domain membership |
| TeX 208–217, 254–283 | Densely defined closable δ; adjoint domain characterized by continuous pairing | This is the intended unbounded domain. Correctly distinguish density of δ-domain, closability, closedness and density of D-domain |
| TeX 504, 674, 703–727 | C_b^∞ cylindrical class; graph-norm and L⁴-graph closure | An algebraic cylindrical class is a collection before closure. D^{1,2} and D^{1,4} are closures in DIFFERENT norms; identifying them with actual adjoint restrictions requires proof |
| TeX 739, 783–810 | Claimed Sobolev identification and divergence-domain extension | Correct the L⁴-derivative inference, use a graph core rather than mere L² density, and distinguish δ from its closure |
| TeX 984–1024, 1054 | Weighted transfer and M-cylindrical density | Weighted transfer needs correct energy spaces. The manuscript itself recognizes an additional M-cylindrical graph-density argument; coordinate generation alone does not prove it |
| TeX 1377 | Claims bounded case bypasses closure by density and invokes unavailable analysis for unbounded case | Boundedness of D only compares its graph norm with L². Product continuity still needs a stronger topology. Distinguish a missing mathematical proof from the work of implementing one |

### Three different objects

1. **Actual domain:** for the fixed δ, dom(D) = dom(δ*) consists of F such that
   u ↦ ⟨F,δu⟩ is continuous in the ambient L² norm of u. For dense δ-domain this
   is equivalent to existence of a unique vector v with ⟨v,u⟩ = ⟨F,δu⟩ for every
   u in dom(δ). The value DF is that representer. For bounded everywhere-defined
   δ, dom(D) is all of L².
2. **Algebraic test class:** finite sums and products of selected test functions.
   No density follows from this description. The chosen class in this increment
   is `Algebra.adjoin ℝ S`, where generators S satisfy the concrete divergence
   multiplier conditions below. Smooth bounded cylindrical generators are a
   future specialization, not something automatically proved admissible here.
3. **Graph core / closure:** a linear subspace C contained in dom(D) is a graph
   core if the closure of the graph of D restricted to C is the graph of D.
   Mathlib already expresses this as `LinearPMap.HasCore`. Ordinary L² density
   is insufficient. Graph convergence means both F_n → F and DF_n → v in L²;
   the new `closed_graph_limit` then proves F ∈ dom(D) and DF = v.
   No graph norm is silently placed on the domain subtype in our definitions.

A fourth-moment restriction is F ∈ dom(D), F ∈ L⁴ and DF ∈ L⁴(H).
`fourthMomentDomain` defines exactly that set of actual domain elements.
It is not defined as a closure and is not identified with classical D^{1,4}.
An L⁴ graph closure additionally requires approximating both F and DF in L⁴.
We have not constructed that closure or proved a density theorem this increment.

### Closedness does not give product closure, even when the product is L²

On (0,1) with Lebesgue probability measure let w(x)=x^(-1/5), and let
D be the maximal multiplication operator Df = wf with domain {f∈L² : wf∈L²}.
This is closed: if f_n→f and wf_n→g in L², simultaneous a.e.-convergent
subsequences give g=wf. It is densely defined: truncation to [1/n,1) approximates
any L² function and w is bounded on each such truncated set.
For f=g=x^(-1/5), wf=x^(-2/5) is L², so f,g∈dom(D).
The product fg=x^(-2/5) is also L², but wfg=x^(-3/5) is not L².
Thus fg∉dom(D). This example is a mathematical counterexample, not a Lean
formalization in this increment, and is not asserted to be a centered divergence.

### Sufficient product-closure hypotheses implemented now

Write M_f^X and M_f^V for pointwise multiplication by f on X=L²(ℝ) and V=L²(H).
For a fixed δ : V →ₗ.[ℝ] X, `IsDivergenceMultiplier δ f` means:

- f is a.e. strongly measurable and essentially bounded;
- M_f^V preserves **δ's** domain;
- there exists a bounded linear R_f : V → X such that, for all u∈dom(δ),

      δ(M_f^V u) = M_f^X(δu) − R_f u.

This is an explicit sufficient analytic condition on the GIVEN δ.
It neither assumes closure of dom(δ*) under products nor prescribes a derivative
of f. The equation determines R_f on the dense δ-domain; `divergenceCommutator_unique`
proves uniqueness of its bounded extension. For an arbitrary unbounded δ, proving
these hypotheses for nonconstant cylindrical generators remains a concrete analytic task.
The criterion is sufficient and may be stronger than needed; no necessity is claimed.

The new proofs show constants, sums and products remain admissible. In particular

    R_(fg) = M_f^X R_g + R_f M_g^V.

All scalar and vector multipliers are actual continuous linear maps constructed
using the preceding L∞ × L² → L² estimates. These are not merely assumed maps.
`boundedMultiplierAlgebra δ` is the resulting subalgebra of real functions on Ω.
Its raw functions have canonical a.e. L² classes on finite measure spaces;
`boundedToL2_mul` proves that algebraic multiplication agrees with actual L² multiplication.
The raw-function algebra is not claimed to inject into L² (null-set differences remain).

For dense δ-domain, admissibility implies M_f^X maps dom(δ*) into itself.
The proof verifies the adjoint relation with the genuine representer

    M_f^V(δ*F) + R_f*F.

If δ is centered, constant one belongs to dom(δ*). Multiplying that constant
proves each admissible f, and every product of admissible f,g, has its L² class
in the actual adjoint domain. Hence the algebraic test class generated by any
admissible generator set is product-closed in dom(δ*), without per-product
membership assumptions. The generator hypotheses must still be proved in applications.
For bounded δ on the whole space, all essentially bounded f satisfy the criterion:
R_f = M_f^X δ − δ M_f^V. This case is verified independently of any Leibniz rule.

### Operator membership is separate from the Leibniz identity

The present theorems do NOT identify R_f u with ⟨Df,u⟩ pointwise, or R_f*G
with G Df. That local identification is needed to obtain
D(fg) = f Dg + g Df. It requires a genuine derivative/IBP construction for the
specific δ, rather than an arbitrary assignment to coordinate derivatives.

For example, on a two-point equal-probability space let δ = I − E on real L²,
where E is projection onto constants. This δ is bounded, centered and self-adjoint,
so D=δ and all bounded multipliers belong to our algebra. For F taking values ±1,
DF=F but D(F²)=D1=0 while 2FDF=2. Product-domain closure therefore does not imply
Leibniz, even with a centered δ and D1=0. This is documented mathematics, not an
additional Lean counterexample theorem.

A restricted Leibniz statement should quantify over elements of a verified test
algebra already included in dom(D), and then assert the identity for the SAME D.
For an L⁴ extension, first establish product membership using known core products,
actual core Leibniz identities, L⁴ value-and-derivative approximation, Hölder
product convergence and closedness. Only then identify the value of D(FG).
Avoid defining a everywhere-valued defect involving D(FG) before its membership
is known. No such extension or cylindrical derivative is implemented here.

### Downstream repairs and remaining arguments

| Results | What this increment supplies | What remains |
| --- | --- | --- |
| D_closed, D_adjoint, adjoint uniqueness, bounded/unbounded agreement | Actual-domain characterization, bounded full-domain theorem, graph-limit criterion | Concrete δ, density and any closability/closedness assumptions |
| `mul_dom`, `mul_cyl`, cylindrical product admissibility | Proven restricted algebra product closure, including generated classes | Verify divergence multiplier conditions for intended cylindrical generators; no all-dom(D) closure |
| `ibp_rep`, D_eq_malliavin and cylindrical Leibniz | A place to state genuine identities without fake domains | True smooth derivatives, representation independence and IBP against the given δ |
| `cylindrical_implies_leibniz`, Gaussian/fBM Leibniz | Correct distinction between algebraic class and graph closure; L⁴ product-term membership | L⁴ derivative estimates, approximation of values AND derivatives, genuine core Leibniz and product-convergence implementation |
| Divergence product rule | Admissible multipliers preserve dom(δ); adjoint membership is proved separately | Identify R_f with the pointwise contraction; for weaker unbounded multipliers, prove graph-core extension and δ = D* (or use δ's closure) |
| Powers / chain rules | Finite products of admissible bounded tests stay in the algebra and actual D-domain | Actual Leibniz, smooth composition admissibility, derivative identities and convergence estimates |
| Clark–Ocone/GKW/variance | Native Hilbert domains unaffected by the erroneous algebra fields | PRP, projection-domain invariance, closed range/isometry and representation hypotheses |
| Brackets / Itô formulas / time integration | Correct prerequisites can now be stated | L⁴ estimates for derivatives/projections, correction integrability, local operator identities, time limits and Fubini; intentionally out of scope |
| Stochastic volatility | Domain restrictions cannot be hidden in total L² multiplications | Genuine weighted energy spaces, transfer domains, and M-cylindrical graph-density analysis |

Mathematical gaps: verifying the test generators against a concrete δ, identifying
its adjoint with a genuine derivative, proving graph density, and proving the required
projection/weighted estimates. Lean implementation work: packaging a known graph topology,
Lp representative compatibility, and sequential Hölder convergence once those mathematical
hypotheses are available. An implementation difficulty is not evidence for any missing
mathematical claim.

### Every new declaration and its meaning

All names are in `OperatorDerivativeRewrite.Foundation`.

| Declaration | Precise meaning |
| --- | --- |
| `mem_adjoint_domain_iff_representable` | For dense δ-domain, F∈dom(δ*) iff a vector represents ⟨F,δu⟩ against every u∈dom(δ) |
| `bounded_adjoint_domain` | The partial adjoint of an everywhere-defined continuous δ has domain ⊤ |
| `closed_graph_limit` | Convergence of both inputs and actual operator outputs for a closed D proves limit membership and identifies D's value |
| `fourthMomentDomain` | Set of elements of the actual D-domain having both value and actual output in L⁴ |
| `fourthMomentDomain_product_terms` | Two such elements yield FG, F DG, G DF in L²; no product-domain membership or identity is asserted |
| `boundedMultiplier` | Continuous linear multiplication by a given MemLp-∞ real function on L²(H) |
| `boundedMultiplier_coeFn` | That map agrees a.e. with pointwise scalar multiplication |
| `boundedMultiplier_add` | M_(f+g) = M_f + M_g |
| `boundedMultiplier_mul` | M_(fg) = M_f composed with M_g |
| `boundedMultiplier_const` | M_c = c times the identity |
| `boundedMultiplier_symmetric` | Real bounded multipliers satisfy ⟨M_fu,v⟩ = ⟨u,M_fv⟩ |
| `IsDivergenceMultiplier` | Explicit δ-domain preservation and bounded divergence commutator, plus MemLp-∞ membership |
| `isDivergenceMultiplier_const` | Constants satisfy that criterion for every linear δ |
| `IsDivergenceMultiplier.add` | Sum admissibility, derived using R_f + R_g |
| `IsDivergenceMultiplier.mul` | Product admissibility, derived using M_f R_g + R_f M_g |
| `boundedMultiplierAlgebra` | Subalgebra whose carrier is exactly the above admissibility predicate; its algebra laws are proved |
| `isDivergenceMultiplier_bounded` | Every MemLp-∞ f is admissible for a continuous δ with whole-space domain |
| `divergenceCommutator_unique` | For dense δ-domain, two bounded commutators obeying the actual equation are equal |
| `adjoin_le_boundedMultiplierAlgebra` | Admissibility of generators implies admissibility of every element of their Mathlib-generated algebra |
| `IsDivergenceMultiplier.preserves_adjoint_domain` | Admissible f preserves the actual δ* domain, for dense δ-domain and complete H |
| `boundedToL2` | Canonical L² a.e. class of an essentially bounded scalar function on a finite measure space |
| `boundedToL2_coeFn` | That class agrees a.e. with its input function |
| `boundedToL2_mul` | The L² class of fg is M_f applied to the L² class of g |
| `one_mem_adjoint_domain` | Centered δ puts constant one in its adjoint domain, on a finite measure space with complete H |
| `IsDivergenceMultiplier.mem_adjoint_domain` | With centered, densely defined δ, each admissible bounded f has its actual L² class in dom(δ*) |
| `multiplierAlgebra_product_mem_adjoint_domain` | Under those hypotheses, every product in the chosen multiplier algebra has its actual L² class in dom(δ*) |
| `generatedAlgebra_product_mem_adjoint_domain` | The same product-domain conclusion for an algebra generated by any family satisfying the explicit δ-multiplier conditions |

Verification: `lake build` and `lake build Foundation.AxiomAudit` succeed. All 27
new definitions/theorems have explicit `#print axioms` commands and report only
`propext`, `Classical.choice`, `Quot.sound`. There is no `sorryAx` or custom axiom.
No original source, existing adjoint/product theorem, full cylindrical derivative
or Itô formula has been altered or implemented by this milestone.

## Genuine Gaussian polynomial core (continuation from 519ff572)

### Original defect and manuscript scope

`OperatorDerivative.lean:2939–2960` defines `CylindricalFunctional` with
independent `f_eval`, `df_eval`, `F`, and `dF`. Neither differentiability nor an
identity relating `df_eval` to the derivative of `f_eval` is required.
`malliavin_derivative_of_cylindrical` at 3005 sums these freely supplied data.
`IsonormalIsGaussian.per_coord_stein` at 3840 and `SteinLemma.stein` at 3903
assume the desired integration-by-parts identities for every such object.
The Gaussian marginal law alone cannot justify those fields. For example, in
one standard Gaussian coordinate, choose f=0 but df=1. Both are integrable and
satisfy the structure's evaluation specifications, yet the claimed Stein identity
would be 0=1. Thus this is a mathematical defect, not an API difficulty.

`cylindrical_compose` at 4892 prescribes the new coefficient as φ'(f)df.
`cylindrical_chain_rule` at 4920 closes by unfolding and `rfl`; it does not prove
that the original df is an actual derivative. Those constructions are not reused.
The manuscript (notably lines 100–104 and its cylindrical-core discussion near
703) intends smooth bounded finite-dimensional functions, an actual IBP formula,
and analytic closure/density arguments. Its intended statements are not silently
replaced by the smaller statements below. The originals remain unchanged.

### Precisely delimited first milestone

The new modules work on Ω=ℝ with γ=gaussianReal 0 1 and H=ℝ. The coordinate
W(h)(x)=hx has law N(0,h²), including the degenerate h=0 case. This is the
rank-one Gaussian model, not an arbitrary isonormal process on an arbitrary H.
A cylinder is F=p(W(h)), where p is an actual real polynomial. Pullback along
W(h) gives `coordinatePolynomial h p = p.comp (C h * X)`.
Every polynomial pullback is smooth and belongs to every finite Lp, by Mathlib's
Gaussian moment theorem; no integrability requirement is presumed without proof.
This polynomial core includes unbounded cylinders and is not the manuscript's
C_b^∞ core. No finite-dimensional generalization or infinite-dimensional result
is claimed here.

The derivative is the classical derivative of actual evaluation, transported
into Mathlib's L² classes. Its formula is DF(x)=p'(hx)h a.e. Equality of continuous
representatives a.e. for γ implies equality everywhere: γ and Lebesgue measure
are mutually absolutely continuous and Lebesgue measure is positive on open sets.
Consequently different polynomial and coordinate representations of the same F
have equal derivatives as L² classes. This includes h=0; no division by h or
nondegeneracy assumption on the chosen coordinate is needed.

The polynomial derivative and divergence are actual `LinearPMap`s with the same
algebraic domain C=range(polynomialEmbedding), not separately specified outputs.
Their graphs are respectively {(p,p')} and {(q,xq-q')} in Gaussian L²×L². We prove
that these graphs determine functions before invoking `Submodule.toLinearPMap`
(which otherwise has a fallback zero map). Products remain in C because they
are actual polynomials with all finite Gaussian moments. Product membership is
proved separately from the derivative's Leibniz equality.

Gaussian IBP is proved by differentiating the explicit Gaussian density and
applying Mathlib's integration by parts on the real line. The hypotheses of that
analytic theorem—integrability of pρ, p'ρ, and xpρ—are all derived from the
Gaussian moment estimates. The resulting identities are

- ∫ xp dγ = ∫ p' dγ;
- ⟨Dp,q⟩ = ⟨p,δq⟩, where δq=xq-q'.

Closability of D in all of L²(γ) is proved without a polynomial-density assumption.
The IBP identity extends continuously to the closure of its graph. For a vertical
limit (0,v), it implies ⟨v,q⟩=0 for every polynomial q. Also v belongs to the
closure of the polynomial subspace, since every derivative p' is polynomial.
Continuity extends the orthogonality to that closed subspace, including v itself;
thus ⟨v,v⟩=0 and v=0. The graph closure therefore is the graph of a genuine
operator, and Mathlib's operator closure is closed.

### Exact meanings of new declarations

All names below are in `OperatorDerivativeRewrite.Foundation.GaussianCore`.

| Declaration | Verified mathematical meaning |
|---|---|
| `γ` | Standard real Gaussian probability measure |
| `polynomial_memLp` | p(x) belongs to L^r(γ) for every r≠∞, including r=0 |
| `polynomial_smooth` | Polynomial evaluation is C^∞ |
| `polynomial_hasDerivAt` | Its actual classical derivative is p'(x) |
| `continuous_representation_unique` | Continuous functions equal γ-a.e. are equal pointwise |
| `derivative_representation_independent` | Polynomial evaluations equal a.e. have identical derivative evaluations |
| `derivative_product` | Actual classical derivative of p(x)q(x) is p'q+pq' |
| `derivative_chain` | Actual derivative of p(q(x)) is p'(q(x))q'(x) |
| `density_hasDerivAt` | Standard Gaussian density has derivative -xρ(x) |
| `integrable_density_mul` | Gaussian integrability implies Lebesgue integrability after multiplication by ρ |
| `polynomial_stein` | Unconditional Stein identity for every polynomial p |
| `divergencePolynomial` | Actual polynomial xq-q' |
| `polynomial_integration_by_parts` | ∫p'q dγ = ∫p(xq-q') dγ |
| `W` | Actual coordinate function hx |
| `W_gaussian_law` | Its pushforward law is N(0,h²) |
| `coordinatePolynomial` | Actual polynomial pullback p(hx) |
| `coordinatePolynomial_eval` | Evaluation equals p(W(h)(x)) |
| `cylindrical_hasDerivAt` | Actual chain derivative is p'(W(h)(x))h |
| `coordinate_not_memLp_top` | x↦x is not in L∞(γ) |
| `GaussianL2` | Mathlib's real L²(γ) Hilbert space |
| `polynomialL2` | Canonical L² class of actual polynomial evaluation |
| `polynomialL2_coeFn` | The class agrees a.e. with polynomial evaluation |
| `polynomialEmbedding` | Linear evaluation map from real polynomials into L²(γ) |
| `polynomialEmbedding_injective` | Equality of polynomial L² classes implies equality of polynomials |
| `polynomialL2_inner` | Their Hilbert pairing is ∫pq dγ |
| `polynomialL2_integration_by_parts` | The genuine polynomial IBP in Hilbert-space notation |
| `derivativeGraph` | Linear range of p↦([p],[p']) |
| `derivativeGraph_vertical_zero` | That range has no nonzero vertical elements |
| `polynomialDerivative` | Partially defined derivative reconstructed from the verified graph |
| `polynomialDerivative_graph` | Its graph is exactly derivativeGraph, not the fallback zero construction |
| `polynomialDerivative_polynomial` | ([p],[p']) belongs to the actual derivative graph |
| `closed_graph_ibp` | IBP holds for every pair in the graph closure and every polynomial test |
| `closed_derivativeGraph_vertical_zero` | The graph closure has no nonzero vertical elements |
| `polynomialDerivative_isClosable` | Genuine closability in all of Gaussian L² |
| `polynomialDerivative_closure_isClosed` | Mathlib's graph closure of D is closed |
| `divergenceLinear` | Linearity of q↦xq-q' |
| `divergenceGraph` | Linear range of q↦([q],[xq-q']) |
| `divergenceGraph_vertical_zero` | That range also determines a genuine operator |
| `polynomialDivergence` | Genuine partially defined polynomial divergence |
| `polynomialDivergence_graph` | Its graph equals divergenceGraph |
| `polynomialDerivative_formalAdjoint` | D and δ obey the formal-adjoint identity on their actual domains |
| `polynomial_mem_divergence_adjoint_domain` | Every polynomial lies in the actual δ* domain, via its proven derivative representer |
| `polynomial_product_graph` | ([pq],[p'q]+[pq']) belongs to D's graph: genuine closure and Leibniz rule |
| `cylindricalL2` | Actual L² class F=p(W(h)) |
| `cylindricalL2_coeFn` | Its a.e. evaluation formula |
| `cylindricalDerivativeL2` | Derivative of the actual pullback polynomial as an L² class |
| `cylindrical_operator_graph` | The cylinder and this derivative belong to D's actual graph |
| `cylindricalDerivativeL2_coeFn` | DF=p'(W(h))h a.e. |
| `cylindrical_representation_independent` | Equal F represented by (h,p) and (k,q) have equal derivative L² classes |
| `coordinate_not_admissible` | x↦x fails the previous IsDivergenceMultiplier criterion |
| `constant_admissible` | Constants satisfy that criterion for the genuine polynomial divergence |
| `polynomialDerivative_domain` | dom D equals the algebraic polynomial L² range |
| `polynomialDivergence_domain` | dom δ equals that same range |

### Multiplier and adjoint conclusions; remaining analytic obligations

The polynomial algebra has genuine product closure, but does not generally
satisfy the bounded-multiplier criterion of the previous milestone. Already
W(1)=x is not essentially bounded, as proved using Gaussian full support and
continuity; hence it cannot satisfy `IsDivergenceMultiplier`. Constants do satisfy
the full criterion, including domain preservation. We do not assert that all
polynomials are bounded multipliers, or that arbitrary bounded smooth functions
preserve the polynomial δ-domain. For example, multiplication by sin(x) sends
constant 1 outside that algebraic polynomial domain. The latter observation is
mathematical explanation, not an additional Lean theorem in this milestone.
A nonconstant bounded smooth core needs an appropriate divergence test domain
and a proof of the commutator's boundedness and domain preservation.

The proven formal-adjoint identity and polynomial membership in dom δ* are
an exact connection with the adjoint foundation at this stage. Identifying
δ*([p]) with [p'] as the value of Mathlib's adjoint requires a dense δ-domain.
Polynomial density in all L²(γ) is mathematically true but is NOT proved or assumed
in these modules. This matters because Mathlib's `LinearPMap.adjoint` uses a
fallback zero value for nondense domains. Neither formal adjointness nor an
existing derivative representer alone licenses claiming equality of that value.
After proving density, the existing `LinearPMap.adjoint_apply_eq` will identify
δ* on the core. Equality of δ* with the closed derivative on its full domain
requires a further argument establishing maximality/core properties; it is not
claimed merely from an inclusion on polynomials.

Remaining work: polynomial density; exact adjoint identification on the core;
full-domain identification if intended; multivariate joint Gaussian IBP and
representation independence for arbitrary finite cylinders (including redundant
coordinates); extension to arbitrary H and isonormal processes; bounded smooth
cylinders and their genuine divergence-domain multiplier estimates; closure
chain/product rules under the proper L⁴ or bounded-factor hypotheses. No Itô,
Clark–Ocone, PRP, or stochastic Fubini assertion follows from this milestone.
The old cylindrical constructions and assumption-based Stein classes remain
unported. Original scalar–constant-vector multiplication and the adjoint
infrastructure remain reusable after the missing hypotheses are actually proved.

Verification: `lake build` and `lake build Foundation.AxiomAudit` succeed.
`lake env lean Foundation/AxiomAudit.lean` checks every declaration explicitly.
All 53 new declarations, including definitions and abbreviations, have axiom
queries. Their dependencies are contained in `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axiom occurs. All 111 declarations in the
combined foundation audit report that same allowed union. A source scan finds
no `sorry`, `admit`, or custom axiom in the foundation modules. Original SHA-256
hashes remain unchanged: Lean `9B8BA956878B80F3C2AC8F239D335C0F49582C88D0693E63554F481ACBEBDF29`;
manuscript `FCA841CCA43DC712AAD2FCF02CB04010ABD7CFCDA4A231022D58A3B23D3BB983`.

## Gaussian density and adjoint inclusions (continuation from aac876f)

### Operator directions and exact domains

Write C=range(polynomialEmbedding) in L²(γ), γ=N(0,1). The original verified
operators are D₀=polynomialDerivative and δ₀=polynomialDivergence, both maps
L²(γ) ⇀ L²(γ) with domain exactly C. Their graphs contain ([p],[p']) and
([q],[xq-q']), respectively. The IBP orientation is ⟨D₀p,q⟩=⟨p,δ₀q⟩.
In particular the derivative is contained in the divergence's adjoint, not in
its own adjoint. Neither algebraic operator is identified with a closed operator
merely from its name or domain density.

### Noncircular density proof now verified

`Foundation/GaussianDensity.lean` proves `polynomialEmbedding_dense` in the whole
Gaussian L² space. The proof does not assume any adjoint identity, Hermite basis,
or density theorem for a graph norm. Searches found compact-set Weierstrass
approximation but no direct Gaussian L² polynomial-density theorem in this
Mathlib checkout. Compact approximation alone would not control polynomial growth
outside the compact set.

First, `finite_measure_eq_of_moments` proves a reusable determinacy result for
finite measures on ℝ with integrable exp(tx) for every real t. Their complex MGFs
are entire by Mathlib's `analyticAt_complexMGF`. The moments determine all complex
derivatives at zero by `iteratedDeriv_complexMGF`; the entire Taylor-series
theorem then makes the MGFs equal everywhere. Mathlib's
`Measure.ext_of_complexMGF_id_eq` turns this into equality of measures. This is
an analytic proof of moment determinacy, not an assumption of it. Requiring
exponential moments is essential: finite moments alone do not generally determine
a measure.

For f∈L²(γ) orthogonal to polynomials, define w₊=max(f,0) and w₋=max(-f,0), and
finite positive measures ν₊=w₊γ and ν₋=w₋γ. The weights belong to L² and L¹.
Gaussian exp(tx) belongs to L² because its squared norm integrates exp(2tx),
whose integrability is already proved in Mathlib. The previous foundation's
`mul_L2_integrable` therefore proves every exponential moment of ν₊ and ν₋.
The same estimate proves integrability of w₊xⁿ and w₋xⁿ. Orthogonality to xⁿ
makes their moments equal. Moment determinacy gives ν₊=ν₋; uniqueness of
withDensity densities gives w₊=w₋ a.e., hence f=0. Finally, the orthogonal
complement of the closed polynomial subspace is zero, so Hilbert projection
implies that subspace is all L²(γ). No desired operator equality appears in this
argument or its hypotheses.

### Exact proved operator conclusions

Define D̄=closure(D₀) and δ̄=closure(δ₀), meaning closure of their graphs in
L²(γ)×L²(γ), reconstructed as genuine single-valued operators. D₀'s closability
was proved in the previous milestone. δ₀'s closability is now proved from its
inclusion in the closed operator D₀*. All four operators D₀, δ₀, D̄, δ̄ have
dense domains; D̄ and δ̄ are closed.

The following are verified inclusions of `LinearPMap`s, so each includes both
operator-domain inclusion and equality of the values on the smaller domain:

- D₀ ⊆ δ₀* and δ₀ ⊆ D₀*;
- D̄ ⊆ δ₀* and δ̄ ⊆ D₀*;
- D̄ ⊆ δ̄* and δ̄ ⊆ D̄*.

The following equalities are also verified: D̄*=D₀* and δ̄*=δ₀*. These are
invariance of each operator's adjoint under its own graph closure. They are not
an identification of D̄ with δ₀*, or of δ̄ with D₀*.
Integration by parts extends to the two closed domains:
∀f∈dom D̄, ∀u∈dom δ̄, ⟨D̄f,u⟩=⟨f,δ̄u⟩.

Every polynomial belongs to dom D̄ and D̄[p]=[p']. It also belongs to dom δ̄
with δ̄[p]=[xp-p']. The actual values δ₀*[p]=[p'] and D₀*[p]=[xp-p'] are now
established on the polynomial core via graph membership; the nondense-domain
fallback previously noted is ruled out by the new density proof. For a genuine
cylinder F=p(W(h)), membership in dom D̄ is proved separately, and D̄F agrees
a.e. with p'(W(h))h for any chosen proof of that membership.

### Why full identification is not claimed

D₀⊆δ₀* follows from IBP and dense δ₀-domain. Since δ₀* is closed, closability
then gives D̄⊆δ₀*. Neither step proves the reverse inclusion δ₀*⊆D̄.
The missing statement is polynomial graph-norm density in dom δ₀*: for every
(f,v)∈graph δ₀*, polynomial pairs ([pₙ],[pₙ']) must converge to (f,v).
Similarly, δ̄=D₀* requires polynomial divergence pairs ([qₙ],[xqₙ-qₙ']) to
approximate every graph pair of D₀*.

The polynomial domain is proved to be a core of D̄ and δ̄, their own closures.
That fact is a consequence of the definition of graph closure. It does NOT prove
that it is a core of δ₀* or D₀*, which may have larger graph domains. Ordinary
L² density concerns only first components and does not prove either graph
approximation. The three assertions D₀⊆δ₀*, D̄=δ₀*, and δ̄=D₀* are therefore
not substituted for one another. General biadjoint/closure duality can relate
the two equality assertions under suitable densely defined closable hypotheses,
but that is additional reasoning, not a consequence of formal adjointness alone.

A concrete route to full one-dimensional identification is normalized Hermite
expansion. Mathlib contains the probabilists' Hermite polynomials and their
Gaussian differentiation formula (`RingTheory/Polynomial/Hermite`), but those
files do not supply Gaussian orthogonality, an L² Hermite Hilbert basis, or the
needed graph approximation theorem. A next development could prove
hₙ=Heₙ/√(n!) is a complete orthonormal family, D₀hₙ=√n hₙ₋₁, and
δ₀hₙ=√(n+1) hₙ₊₁. Adjointness would determine weighted coefficient sequences;
finite Hermite truncations would then converge in both graph components. This
would supply the missing reverse inclusions. This paragraph is a proof strategy,
not a list of already verified Hermite theorems.

The milestone stops at the proved closed inclusions; no equality D̄=δ₀* or
δ̄=D₀* is asserted as Lean-verified. No arbitrary-domain assumption equivalent
to either equality has been introduced.

### New declaration meanings

All Gaussian names are in `OperatorDerivativeRewrite.Foundation.GaussianCore`.
The four general lemmas are in `OperatorDerivativeRewrite.Foundation`.

| Declaration | Exact meaning |
|---|---|
| `finite_measure_eq_of_moments` | Finite real measures with every exponential moment and equal polynomial moments are equal |
| `gaussian_exp_memLp_two` | exp(tx)∈L²(γ) for every t |
| `weightedMeasure` | Positive measure μ.withDensity(ofReal w) |
| `weighted_integrable_iff` | For measurable w≥0, g is integrable for wμ iff wg is integrable for μ |
| `weighted_integral` | For such w, ∫g d(wμ)=∫wg dμ |
| `weighted_finite` | A measurable nonnegative integrable density defines a finite measure |
| `eq_zero_of_polynomial_orthogonal` | An L²(γ) function orthogonal to every polynomial is zero |
| `polynomialEmbedding_dense` | The polynomial range is dense in all Gaussian L² |
| `operatorClosure_le_closed` | A closable operator's graph closure lies in every given closed extension |
| `operatorClosure_dense_domain` | Dense original domain implies dense closure domain |
| `formalAdjoint_closure_left` | A genuine formal-adjoint identity extends to the closure of the first operator |
| `operatorClosure_adjoint_eq` | Closing a densely defined closable real Hilbert-space operator leaves its adjoint unchanged |
| `polynomialDerivative_dense_domain` | dom D₀ is dense |
| `polynomialDivergence_dense_domain` | dom δ₀ is dense |
| `polynomialDerivative_le_divergence_adjoint` | D₀⊆δ₀* as actual operators |
| `polynomialDivergence_le_derivative_adjoint` | δ₀⊆D₀* as actual operators |
| `polynomialDivergence_isClosable` | δ₀ has a single-valued graph closure |
| `closedDerivative`, `closedDivergence` | Graph closures D̄ and δ̄ of the actual polynomial operators |
| `closedDerivative_isClosed`, `closedDivergence_isClosed` | Both graph closures are closed operators |
| `closedDerivative_dense_domain`, `closedDivergence_dense_domain` | Both closed operators have dense domains |
| `closedDerivative_le_divergence_adjoint` | D̄⊆δ₀* |
| `closedDivergence_le_derivative_adjoint` | δ̄⊆D₀* |
| `closedDerivative_formalAdjoint` | IBP between all members of the two closed domains |
| `closedDerivative_polynomial_graph` | ([p],[p'])∈graph D̄ |
| `closedDivergence_polynomial_graph` | ([p],[xp-p'])∈graph δ̄ |
| `divergence_adjoint_polynomial_graph` | ([p],[p'])∈graph δ₀* |
| `derivative_adjoint_polynomial_graph` | ([p],[xp-p'])∈graph D₀* |
| `closedDerivative_has_polynomial_core` | C is a graph core for D̄ itself |
| `closedDivergence_has_polynomial_core` | C is a graph core for δ̄ itself |
| `closedDerivative_adjoint_eq` | D̄*=D₀* |
| `closedDivergence_adjoint_eq` | δ̄*=δ₀* |
| `closedDerivative_le_closedDivergence_adjoint` | D̄⊆δ̄* |
| `closedDivergence_le_closedDerivative_adjoint` | δ̄⊆D̄* |
| `closedDerivative_polynomial_mem` | Membership of every polynomial in dom D̄ |
| `closedDerivative_polynomial_apply` | D̄[p]=[p'] for any proof of membership |
| `closedDerivative_cylindrical_mem` | Membership of every existing one-coordinate polynomial cylinder in dom D̄ |
| `closedDerivative_cylindrical_coeFn` | Its closed derivative is p'(W(h))h a.e. |

The closure/formal-adjoint lemmas apply to general real inner-product spaces
(and complete spaces where actual adjoints are used), so are reusable for scalar
and vector-valued multivariate domains. Moment determinacy applies to arbitrary
finite measures on ℝ with exponential moments, not only γ. Multivariate density,
Hermite tensor bases, and their graph norms remain future work.

Verification for this milestone: `lake build` and `lake build Foundation.AxiomAudit`
both succeed. All 40 new declarations have explicit axiom queries; the combined
151-declaration audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx`, custom axioms, `sorry`, or `admit` occur. The new modules emit no
compiler or linter warnings; the pre-existing unused-section-variable warnings
in `Foundation.Adjoint` remain. The original Lean and manuscript hashes are
unchanged, and the prior verified Gaussian core modules have not been modified.

## Hermite spectral identification (continuation of 68d3189)

This section resolves the one-dimensional graph-core and adjoint-identification
obligations recorded in the preceding milestone. The underlying measure is still
γ = N(0,1), and the original polynomial operators are unchanged:

- dom D₀ = dom δ₀ = C = polynomialEmbedding.range;
- D₀[p] = [p']; δ₀[p] = [xp-p'];
- D̄ and δ̄ are their actual graph closures as Mathlib `LinearPMap`s.

### Construction and proof dependencies

`Foundation/GaussianHermite.lean` maps Mathlib's integer-coefficient
`Polynomial.hermite n` to real coefficients. Its recursion is precisely
H₀ = 1, Hₙ₊₁ = xHₙ-Hₙ'. The lowering formula Hₙ₊₁' = (n+1)Hₙ is proved
by induction using the actual polynomial commutator Dδp = p+δDp.
Gaussian integration by parts then yields
⟨Hₙ,Hₘ⟩ = 1_{n=m} n!, including the probability normalization at degree zero.
No Rodrigues formula, Gaussian orthogonality, or spectral identity is assumed.

Define eₙ = [Hₙ]/√(n!). Positivity of n! proves that these normalizers are
nonzero. The eₙ are orthonormal. Monicity and degree Hₙ = n give an algebraic
polynomial sequence spanning all real polynomials via Mathlib
`Polynomial.Sequence.span`. Consequently span{eₙ} = C. The independently
proved `polynomialEmbedding_dense` supplies completeness; Mathlib
`HilbertBasis.mk` gives a genuine isometric coefficient representation in ℓ².
In particular, cₙ(f) = ⟨eₙ,f⟩, and f = Σ cₙ(f)eₙ in L².

The verified actual polynomial graph actions are
D₀e₀ = 0, D₀eₙ₊₁ = √(n+1)eₙ, δ₀eₙ = √(n+1)eₙ₊₁.
All these vectors already have justified L² integrability from the polynomial
moment theorem. Coefficients and derivative values are never prescribed
independently of the functions.

### Spectral argument for the missing graph cores

Let P_N f = Σ_{n<N} cₙ(f)eₙ. These truncations converge to f in L² for every
f, without any operator assumption.

For (f,g) in graph δ₀*, test the actual adjoint identity against eₙ in dom δ₀.
It forces cₙ(g) = √(n+1)cₙ₊₁(f). The lowering actions give, by finite induction,
(P_{N+1}f, P_N g) in graph D₀. Both components converge to (f,g), so this pair
belongs to graph D̄. This proves δ₀* ⊆ D̄; combine with the already proved
opposite inclusion to obtain D̄ = δ₀*.

For (f,g) in graph D₀*, testing e₀ and eₙ₊₁ forces c₀(g)=0 and
cₙ₊₁(g)=√(n+1)cₙ(f). The raising actions give
(P_N f, P_{N+1}g) in graph δ₀, converging to (f,g). Hence D₀* ⊆ δ̄ and,
using the previous opposite inclusion, δ̄ = D₀*.

These are separate verified approximation arguments in the two directions.
They use only Hilbert-basis completeness, the true adjoint graph equation, and
the actual ladder actions. Graph-norm density is a conclusion, never a
hypothesis. The conditional coefficient-to-graph lemmas are sufficiency
proofs by explicit approximation; necessity is proved by adjoint testing.
Together they give exact graph characterizations, not a conditional operator
interface. Product-topology convergence of input and output is equivalent to
convergence in the Hilbert graph norm √(‖input‖²+‖output‖²).

Closing either densely defined operator leaves its adjoint unchanged, so the
strongest proved identities are

    D̄ = δ₀* = δ̄*,       δ̄ = D₀* = D̄*.

The pre-existing polynomial graph and application theorems still identify
D̄[p]=[p'] and δ̄[p]=[xp-p']; the equalities therefore preserve exactly the
original polynomial operators. The previous classical cylindrical derivative
formula also remains valid. No original source or manuscript was edited.

### Exact weighted domains and norms

Parseval is proved as `HasSum (fun n => cₙ(f)^2) ‖f‖²`. Conversely, every
square-summable real sequence is realized by the inverse Hilbert-basis
isometry. This is a theorem, not an existence or integrability assumption.

The closed graph characterizations imply, for f already in Gaussian L²,

    f ∈ dom D̄  ↔  Σ n cₙ(f)² < ∞,
    f ∈ dom δ̄  ↔  Σ (n+1)cₙ(f)² < ∞.

Lean expresses these convergent real series with `Summable`. The two domains
are proved equal because Σ cₙ(f)² is already finite. Their output norms and
Hilbert graph norms are exactly

    ‖D̄f‖² = Σ n cₙ(f)²,
    ‖δ̄f‖² = Σ (n+1)cₙ(f)²,
    ‖f‖² + ‖D̄f‖² = Σ (n+1)cₙ(f)²,
    ‖f‖² + ‖δ̄f‖² = Σ (n+2)cₙ(f)².

`HasCore` is established for span{eₙ} in each full adjoint domain. The two
explicit approximation theorems additionally exhibit the polynomial graph
sequences and their convergence for every adjoint graph pair.

### Meaning of all new public declarations

All names below are in `OperatorDerivativeRewrite.Foundation.GaussianCore`.
The two private inner-product recurrence lemmas are proved by IBP and are
included transitively in the axiom audit of `hermiteVector_inner`.

| Declaration | Precise meaning |
|---|---|
| `hermitePolynomial` | Real-coefficient image of Mathlib's probabilists' Hₙ |
| `hermitePolynomial_zero` | H₀=1 |
| `hermitePolynomial_succ` | Hₙ₊₁=δHₙ for the original differential expression |
| `derivative_divergencePolynomial` | (xp-p')'=p+xp'-p'' |
| `hermitePolynomial_derivative` | Hₙ₊₁'=(n+1)Hₙ |
| `hermitePolynomial_monic`, `hermitePolynomial_degree` | Hₙ is monic of degree n |
| `hermiteSequence` | The Hermites as Mathlib's degree-indexed polynomial sequence |
| `hermitePolynomial_span` | All real polynomials are finite algebraic Hermite expansions |
| `hermiteVector` | Hₙ evaluated as a Gaussian L² equivalence class |
| `hermiteVector_inner` | ⟨Hₙ,Hₘ⟩=1_{n=m}n! |
| `normalizedHermite` | eₙ=[Hₙ]/√(n!) |
| `hermite_normalizer_pos`, `hermite_normalizer_succ` | Positive √(n!) and its square-root recursion |
| `normalizedHermite_orthonormal` | The eₙ form an orthonormal family |
| `hermiteVector_span`, `normalizedHermite_span` | Each algebraic vector span is exactly C |
| `normalizedHermite_dense_span` | Density of that span in Gaussian L² |
| `hermiteBasis` | The complete normalized Hermite Hilbert basis |
| `hermiteBasis_apply` | Its vectors are precisely eₙ |
| `hermiteBasis_coefficient` | Its isometry coordinates equal ⟨eₙ,f⟩ |
| `hermiteBasis_hasSum` | The coefficient expansion converges unconditionally to f in L² |
| `normalizedHermite_derivative_graph` | (eₙ₊₁,√(n+1)eₙ) belongs to graph D₀ |
| `normalizedHermite_derivative_zero_graph` | (e₀,0) belongs to graph D₀ |
| `normalizedHermite_divergence_graph` | (eₙ,√(n+1)eₙ₊₁) belongs to graph δ₀ |
| `hermiteCoefficient` | The actual real Hilbert pairing cₙ(f) |
| `hermiteTruncation` | P_N f, its actual finite expansion |
| `hermiteTruncation_zero`, `hermiteTruncation_succ` | Empty sum and addition of the next Hermite term |
| `hermiteTruncation_tendsto` | P_N f→f in L² for every f |
| `divergence_adjoint_coefficients` | Necessary lowering coefficient equation for graph δ₀* |
| `derivative_adjoint_coefficient_zero` | Necessary zero-mode equation c₀(g)=0 for graph D₀* |
| `derivative_adjoint_coefficients` | Necessary raising coefficient equation for graph D₀* |
| `hermiteTruncation_derivative_graph` | Lowering coefficient equations produce actual finite D₀ graphs |
| `hermiteTruncation_divergence_graph` | Raising equations and the zero mode produce actual finite δ₀ graphs |
| `closedDerivative_graph_of_coefficients` | Those lowering equations suffice for membership in graph D̄ |
| `closedDivergence_graph_of_coefficients` | Those raising equations and the zero mode suffice for graph δ̄ |
| `closedDerivative_eq_divergence_adjoint` | Full operator equality D̄=δ₀* |
| `closedDivergence_eq_derivative_adjoint` | Full operator equality δ̄=D₀* |
| `closedDerivative_eq_closedDivergence_adjoint` | Full operator equality D̄=δ̄* |
| `closedDivergence_eq_closedDerivative_adjoint` | Full operator equality δ̄=D̄* |
| `closedDerivative_graph_iff`, `closedDivergence_graph_iff` | Exact necessary-and-sufficient spectral graph equations |
| `hermiteCoefficient_hasSum_sq` | Parseval, including square summability and the L² norm |
| `exists_hermite_coefficients` | Existence of an L² vector for any square-summable real sequence |
| `hermite_weight_square` | (√(n+1)a)²=(n+1)a² |
| `closedDerivative_domain_iff` | dom D̄ is exactly the n-weighted coefficient domain |
| `closedDivergence_domain_iff` | dom δ̄ is exactly the (n+1)-weighted coefficient domain |
| `closedDerivative_domain_eq_closedDivergence_domain` | These two closed domains coincide |
| `closedDerivative_norm_sq`, `closedDivergence_norm_sq` | Exact output-norm squared formulas on each closed graph |
| `closedDerivative_graph_norm_sq`, `closedDivergence_graph_norm_sq` | Exact Hilbert graph-norm squared formulas |
| `divergence_adjoint_has_hermite_core`, `derivative_adjoint_has_hermite_core` | Finite Hermite expansions are graph cores for the two full adjoints |
| `divergence_adjoint_hermite_approximation` | Explicit D₀ graph approximants and their joint convergence for each δ₀* graph pair |
| `derivative_adjoint_hermite_approximation` | Explicit δ₀ graph approximants and their joint convergence for each D₀* graph pair |

### Downstream consequences and remaining scope

The one-dimensional adjoint and graph-core gaps are fully resolved for the
standard-Gaussian polynomial operators. They can now serve as actual closed
operators in the existing adjoint framework. This does not prove that the
common closed domain is an algebra, that its functions are bounded, or that
polynomial multiplication is an admissible bounded commutator. The verified
L² product restrictions and the obstruction for the unbounded coordinate
continue to apply.

Multivariate Gaussian tensor bases, directional/vector-valued operators,
representation independence across arbitrary finite Gaussian coordinate
systems, bounded smooth cylindrical domains, admissible nonconstant
multipliers, and the Itô formula remain distinct future obligations. A tensor
Hermite basis and the corresponding directional weighted sums are the natural
next step. No such multivariate or stochastic claims are asserted here.

Verification: the complete `lake build`, `lake build Foundation.AxiomAudit`,
and a fresh `lake env lean Foundation/AxiomAudit.lean` all succeed. The 57 new
public declarations have explicit `#print axioms` queries;
together with the existing 151 queries, the audit covers 208 declarations and
all their transitive proof dependencies. The audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axioms occur.
The new modules have no compiler/linter warnings; the
pre-existing unused-section-variable warnings in `Foundation.Adjoint` remain.

## Finite-dimensional Gaussian cylinder foundation (continuation of a2ccf4b)

This is a deliberately bounded first finite-dimensional milestone: actual
Gaussian coordinates, a representation-independent polynomial L² gradient,
and independent tensor Hermite orthogonality. It does not assert multivariate
polynomial density, tensor completeness, gradient closability, or any
multivariate adjoint identity. Those remain proof obligations, not hypotheses
of an abstract interface. No existing result or original source was changed.

### Ambient measure and mathematical assumptions

Let E be a finite-dimensional real inner-product space with its Borel measurable
structure. No positive dimension or nondegeneracy of a coordinate family is
required. `gaussianMeasure E` is Mathlib's `ProbabilityTheory.stdGaussian E`;
it is not a new axiomatic Gaussian process. For h in E, define W(h)(x)=⟨h,x⟩.
The exact marginal is N(0,‖h‖²), and Cov(W(h),W(k))=⟨h,k⟩. The finite
coordinate family is a continuous linear map, and its pushforward measure is
proved Gaussian. Finite linear relations among the hᵢ hold pointwise among
W(hᵢ). This includes zero vectors, duplicate coordinates, and singular Gram
matrices without pretending they have nondegenerate densities.

For an orthonormal basis b, the coordinate vector (W(bᵢ)) has exactly the
independent product law ∏ᵢγ. This theorem is restricted to orthonormal
coordinates. The law of an arbitrary finite family h has Gram covariance
⟨hᵢ,hⱼ⟩ and may be correlated or supported on a proper linear subspace;
independent tensor formulas are not transferred to that law without proof.

The ambient measure stdGaussian E does have full support. This is proved from
Mathlib's orthonormal product realization, positivity of one-dimensional
Gaussian measure on nonempty open sets, positivity of finite products, and
surjectivity/continuity of orthonormal synthesis. It is used on E, never on a
potentially singular coordinate image.

The scalar polynomial and analytic lemmas do not require finite-dimensional E.
Actual Gaussian statements here do require finite-dimensional E: there is no
standard Gaussian measure on an arbitrary infinite-dimensional Hilbert space
with identity covariance. An isonormal process over an infinite-dimensional
space requires a different probability-space construction and consistency
arguments. No such process or infinite-dimensional Malliavin operator is
claimed by these definitions.

### Genuine derivatives and representation independence

For any finite family h:ι→E and actual `MvPolynomial ι ℝ` p, define

    F(x) = p(W(h₁)(x),...,W(hₙ)(x)),
    G(x) = Σᵢ (∂ᵢp)(W(h)(x)) hᵢ.

The formal partial derivatives are Mathlib's `MvPolynomial.pderiv`, and are
not independently supplied values. Induction on the polynomial proves
`HasFDerivAt F (innerSL ℝ (G x)) x` for every x. Thus G is verified as the
actual Hilbert gradient. Smoothness of F and the analytic product rule are
proved from actual polynomial evaluation and continuous linear coordinates.
The polynomial gradient formula is not itself used as an assumed chain rule.

For cylinders using a common finite family, the gradient product identity is

    ∇(FG) = F∇G + G∇F.

All finite Lp moments of coordinates, cylinders, and their Hilbert-valued
gradients are proved. The multiplication step uses the verified Hölder
infrastructure at exponents 2r,2r→r. Scalar multiplication by the fixed hᵢ
uses Lr×L∞→Lr, and the finite sum gives gradient membership. In particular,
F,G,∇F,∇G are in L⁴ and the product expressions above are in L². No closure
of arbitrary L² under multiplication is invoked. No L∞ membership of a
nonconstant polynomial is asserted.

Suppose p(W(h)) and q(W(k)) agree stdGaussian E-almost everywhere, with
possibly different finite index sets and dependent families. Their continuous
ambient representatives agree everywhere by the proved full support.
Their actual Fréchet derivatives therefore agree; injectivity of the real
Hilbert-to-dual isometry gives equality of the ambient gradients everywhere.
The result is also proved for the actual scalar/vector L² equivalence classes.
This establishes well-defined gradient values independently of any choice of
cylindrical representation.

For example, if h₁=h₂, p(z₁,z₂)=z₁-z₂ represents the zero variable although
its formal coordinate partials are (1,-1). Its genuine ambient gradient is
h₁-h₂=0. Equality of raw coordinate partial arrays is not the required notion
of representation independence. The theorem proves equality of the weighted
ambient vector, so it handles exactly this degeneracy.

### Independent tensor polynomial construction

`FiniteGaussianTensor.lean` defines Hₙ/√(n!) as an actual real polynomial
whose one-dimensional L² class is the previously verified normalized Hermite
basis vector. For finite multi-index α:ι→ℕ, define

    e_α(x) = ∏ᵢ H_{αᵢ}(xᵢ)/√(αᵢ!),    x ∈ ℝ^ι,    measure ∏ᵢγ.

Every partial product has all finite moments by Hölder induction; every full
tensor is therefore a justified L² vector. Product-measure Fubini and the
verified one-dimensional Hermite integrals give

    ⟨e_α,e_β⟩ = 1_{α=β}.

This proves an orthonormal family, including the empty-index case. It does
not prove that this family is a Hilbert basis. No `HilbertBasis.mk` is applied
with an unproved density assumption. The one-dimensional complete basis is
reused for its exact normalization and orthogonality, while its completeness
has not yet been lifted through product L².

### Meaning of all new declarations

All names below are in `OperatorDerivativeRewrite.Foundation.FiniteGaussian`.

| Declaration | Mathematical meaning |
|---|---|
| `gaussianMeasure` | Mathlib's basis-independent standard Gaussian on finite-dimensional E |
| `coordinate`, `coordinate_apply` | The continuous linear functional W(h)=⟨h,·⟩ and its pointwise value |
| `gaussianMeasure_openPos` | Positivity of the ambient Gaussian on every nonempty open set |
| `continuous_ae_eq` | Continuous scalar ambient representatives equal a.e. are equal everywhere |
| `coordinate_memLp` | Every W(h) has every finite Lp moment |
| `coordinate_gaussian_law` | W(h) has the exact possibly degenerate marginal N(0,‖h‖²) |
| `coordinate_covariance` | Cov(W(h),W(k))=⟨h,k⟩ |
| `coordinate_add`, `coordinate_smul`, `coordinate_linear_relation` | True pointwise linear relations among coordinates |
| `gaussianMeasure_eq_product_map` | Product-Gaussian realization through any orthonormal basis |
| `coordinateFamily` | The finite joint coordinate continuous linear map |
| `coordinateFamily_isGaussian` | Gaussianity of its pushforward, with no rank assumption |
| `orthonormal_coordinates_joint_law` | Exact independent product law for an orthonormal basis family |
| `cylinder` | Actual multivariate polynomial evaluation at W(h) |
| `cylinderGradient` | The computed vector Σᵢ(∂ᵢp)(W(h))hᵢ |
| `cylinder_C`, `cylinder_X`, `cylinder_add`, `cylinder_mul` | Evaluation respects constants, variables, addition, and multiplication |
| `cylinderGradient_C`, `cylinderGradient_X`, `cylinderGradient_add` | Computed constant/coordinate gradients and additivity |
| `cylinderGradient_mul` | Polynomial vector product identity, subsequently verified analytically |
| `cylinder_hasFDerivAt`, `cylinder_fderiv` | The computed vector represents the actual Fréchet derivative |
| `cylinder_smooth`, `cylinder_continuous` | Actual smoothness and continuity of the evaluated cylinder |
| `cylinder_product_rule` | Analytic Fréchet derivative product rule for actual cylinders |
| `doubled_holderTriple` | Proved arithmetic (2r)⁻¹+(2r)⁻¹=r⁻¹, not a closure axiom |
| `cylinder_memLp`, `cylinderGradient_memLp` | Actual finite-moment integrability of the scalar function and vector gradient |
| `cylinderGradient_representation_independent` | Ambient gradient equality across a.e.-equal finite representations |
| `cylinderL2`, `cylinderGradientL2` | Actual scalar/vector L² equivalence classes with integrability already proved |
| `cylinderL2_coeFn`, `cylinderGradientL2_coeFn` | Their a.e. representatives are the actual functions above |
| `cylinderGradientL2_representation_independent` | Equal scalar L² cylinders have equal vector L² gradients |
| `normalizedHermitePolynomial` | Actual normalized real Hermite polynomial |
| `normalizedHermitePolynomial_L2` | Its one-dimensional class is the previously verified Hermite basis vector |
| `normalizedHermitePolynomial_integral` | Exact integral orthogonality of those scalar representatives |
| `productGaussian` | Actual independent finite product measure ∏ᵢγ |
| `tensorHermiteFunction` | Actual finite product e_α of normalized Hermite representatives |
| `tensorHermite_partial_memLp`, `tensorHermite_memLp` | Proved finite moments of partial and full tensor products |
| `tensorHermite`, `tensorHermite_coeFn` | Actual product Gaussian L² vectors and their a.e. representatives |
| `tensorHermite_inner`, `tensorHermite_orthonormal` | Exact tensor inner products and orthonormality; no completeness assertion |

### Remaining analytic obligations and adjoint investigation

The next formalization task is tensor completeness and finite-dimensional
polynomial density. A valid route is to lift the existing one-dimensional
complete Hermite basis using a proved product/iterated-L² identification and
Fubini, or to prove that a vector orthogonal to all tensor products is zero.
The inspected Mathlib tensor basis API concerns finite algebraic tensor
products and finite-dimensional orthonormal bases; it does not by itself give
this Hilbert completion/density theorem for infinite-dimensional Gaussian L².
The missing result is an implementation/proof obligation for a true theorem,
not a mathematical failure of polynomial density. A fixed family spanning a
proper subspace cannot be assumed dense in the whole ambient L² space.

After density, multivariate IBP still needs a proof by integrable slices and
finite-product Fubini, starting from the verified one-dimensional polynomial
IBP. The intended ambient identity is

    E[⟨∇F,k⟩ G] = E[F (W(k)G-⟨∇G,k⟩)].

It does not require a Gram-matrix inverse. It is not currently a Lean theorem
in these modules. Vector-valued test-core density and this identity should
then prove closability of the actual finite-dimensional gradient. No
closability, dense operator domain, or full divergence adjoint is assumed now.

For future independent Hermite coordinates, the expected closed gradient
domain condition is Σ_α |α| |c_α|²<∞. The divergence output coefficients
should be Σᵢ √(αᵢ) u_{i,α-eᵢ}, with absent/negative indices contributing zero.
Its maximal adjoint domain must control the square-summability of that SUM;
requiring each separate weighted coordinate derivative to be square summable
can be stronger because terms can cancel. These are mathematical targets
only, not verified declarations or asserted domain identities. The existing
one-dimensional domains cannot simply be intersected to obtain the strongest
vector-divergence domain without a new spectral proof.

The original cylindrical interfaces (`OperatorDerivative.lean:340–360` and
the manuscript's cylindrical-reduction discussion) remain untouched. The
actual polynomial derivative and representation-independent L² value now
supply concrete ingredients for repair, but their asserted IBP and closed
operator identifications still require the finite-dimensional analytic steps
above. General bounded smooth cylinders, consistency across growing ambient
spaces, and infinite-dimensional limits remain future work.

Verification for this milestone comprises `lake build`,
`lake build Foundation.AxiomAudit`, and a fresh
`lake env lean Foundation/AxiomAudit.lean`. There are 50 new explicit axiom
queries, for 258 audited declarations in total. The fresh audit reports only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom
axioms. The original Lean/manuscript hashes and all previous foundation source
files are checked unchanged before committing. Only pre-existing warnings in
`Foundation.Adjoint` remain; the new modules have no compiler/linter warnings
and no suppressed linters.

## Finite Gaussian polynomial density and tensor completeness (after 0347f06)

This milestone proves scalar L² completeness, not graph-norm density or a
multivariate adjoint identity. The original Lean and manuscript are unchanged.
The original `UnboundedCylindricalStructure.cyl_dense` at
`OperatorDerivative.lean:347–350` describes graph convergence in a comment but
its field supplies only a sequence of cylindrical functions, with no convergence
condition. The manuscript's cylindrical reduction and closure discussion
(e.g. lines 52, 84 and 165) also needs genuinely proved density and IBP results.
The new theorems below supply the scalar L² density prerequisite; they do not
validate that original graph-density claim.

### Precise setting and noncircular proof

For any finite index type I, μ = ∏ᵢ γ on I → ℝ, with γ = N(0,1). All results
hold for I = Fin n, for every n, with no positivity-of-dimension hypothesis.
The underlying Pi space uses its ordinary finite-product Borel structure;
no correlated-coordinate law is substituted for this independent product.

`Foundation/FiniteGaussianDensity.lean` proves polynomial density without
assuming tensor completeness. If f ∈ L²(μ) is orthogonal to all polynomials,
its positive and negative parts define finite positive measures ν₊ and ν₋.
For every continuous real linear functional L and t ∈ ℝ,
exp(t L(x)) ∈ L²(μ): decompose L into finitely many coordinate functionals,
factor the exponential, and apply the proved one-dimensional exponential
moments and Hölder with doubled exponents. Cauchy–Schwarz then proves all
exponential moments of the pushforwards L_*ν₊ and L_*ν₋. Orthogonality to (L(x))ⁿ gives equal
moments of these projected measures. The previously verified
`GaussianCore.finite_measure_eq_of_moments` makes every pair of projections
equal; Mathlib's `Measure.ext_of_charFunDual` makes ν₊ = ν₋. Uniqueness of
nonnegative densities gives f = 0. Orthogonal-complement theory yields
polynomial density. This also works in dimension zero, where the zeroth
moment fixes the total mass.

`Foundation/FiniteGaussianCompleteness.lean` uses the existing one-dimensional
Hermite polynomial sequence basis, rescaled by 1/√(n!), to expand every
separable polynomial into a finite Hermite tensor sum. Mathlib's
`MultilinearMap.map_sum_finset` performs the finite distributive expansion.
Every multivariate monomial is a scalar multiple of a separable polynomial,
so normalized tensor polynomials span the entire multivariate polynomial
space. Their Gaussian L² classes span exactly the algebraic polynomial core.
Independent polynomial density and the previously verified tensor
orthonormality then construct an actual `HilbertBasis (I → ℕ)`.

The existing one-dimensional complete Hermite basis is preserved and its
agreement with the one-coordinate tensor basis is explicitly verified by
`tensorHermite_unique_coordinate`. The proof of higher-dimensional density
uses the verified one-dimensional moment-uniqueness infrastructure rather
than an unproved Hilbert tensor-completion identification. The inspected
Mathlib algebraic tensor/finite-dimensional orthonormal-basis APIs alone do
not supply that analytic identification. This is an alternative proof of the
requested full completeness theorem, not a conditional or weaker replacement.

### Meanings of all new public declarations

All names below are in `OperatorDerivativeRewrite.Foundation.FiniteGaussian`.
Private helpers establish arbitrary finite exponential moments of γ, finite
products of these exponentials, nonnegative weighted-measure integrability,
integral transfer, finiteness, and the rescaled one-dimensional polynomial
basis. None are postulates.

| Declaration | Verified mathematical meaning |
| --- | --- |
| `productPolynomial_memLp` | Every multivariate polynomial has every finite moment under μ |
| `productPolynomialL2` | The actual L² class of polynomial evaluation, with proved integrability |
| `productPolynomialL2_coeFn` | Its representative equals polynomial evaluation μ-a.e. |
| `productPolynomialEmbedding` | Linear evaluation into L²; its range is the algebraic polynomial core |
| `productGaussian_exp_linear_memLp` | exp(t L(x)) belongs to L²(μ) for every real continuous linear functional L and t |
| `eq_zero_of_productPolynomial_orthogonal` | A vector orthogonal to every polynomial is zero, by the weighted-measure argument |
| `productPolynomialEmbedding_dense` | The algebraic multivariate polynomial core is dense in L²(μ) |
| `tensorPolynomialMap` | The genuine multilinear map (pᵢ) ↦ ∏ᵢ pᵢ(Xᵢ) |
| `tensorHermitePolynomial` | ∏ᵢ H_{αᵢ}(Xᵢ)/√(αᵢ!), an actual multivariate polynomial |
| `tensorPolynomialMap_mem_span` | Every separable polynomial is in the algebraic span of these tensors |
| `tensorHermitePolynomial_span` | Their algebraic polynomial span is the whole multivariate polynomial space |
| `tensorHermitePolynomial_eval` | Evaluation gives the already verified tensor representative e_α(x) |
| `tensorHermitePolynomial_L2` | Its polynomial L² class is exactly the existing tensor vector |
| `tensorHermite_span` | The algebraic tensor-vector span equals the polynomial embedding range |
| `tensorHermite_dense_span` | That span is dense in the full product Gaussian L² space |
| `tensorHermiteBasis` | Complete orthonormal Hilbert basis indexed by I → ℕ |
| `tensorHermiteBasis_apply` | Its basis vector at α is the previously defined tensorHermite α |
| `tensorHermiteBasis_hasSum` | Every f equals the unconditionally convergent sum Σ_α ⟨e_α,f⟩e_α |
| `tensorHermiteFunction_empty` | In dimension zero the sole tensor representative is the constant 1 |
| `tensorHermite_empty_expansion` | Every zero-dimensional L² vector is its vacuum coefficient times the vacuum vector |
| `tensorHermite_unique_coordinate` | For a singleton coordinate index, the tensor vector is the measure-preserving pullback of the existing one-dimensional Hermite Hilbert-basis vector |
| `orthonormal_coordinates_measurePreserving` | Coordinates in an orthonormal basis of the ambient finite Hilbert space preserve its standard Gaussian measure to μ |
| `productPolynomialL2_pullback` | Pullback of polynomial L² evaluation is exactly the existing cylinderL2 b p |
| `tensorHermite_pullback` | Pullback of each tensor vector is the genuine cylinder of its tensorHermitePolynomial |

### Independent, correlated, and degenerate families

The basis and density theorems above concern the independent standard
coordinate space. Compatibility with ambient standard Gaussian cylinders is
proved through orthonormal-basis coordinates. The earlier representation
independence theorems for arbitrary correlated/dependent families remain
unchanged. Their joint law has Gram covariance and may lie on a proper linear
subspace. No tensor orthogonality for such a family, density of its functions
in the entire ambient L² space, or invertible Gram matrix is asserted here.
Density with respect to a degenerate family's own image law and a transported
complete ambient Hilbert basis can be treated separately if needed.

### Remaining analytic prerequisites and downstream consequences

There is no unresolved obstruction to scalar polynomial density or tensor
completeness in this milestone. Their proofs are completed.

* Multivariate polynomial Gaussian IBP still needs integrable slices and
  finite-product Fubini using the verified one-dimensional IBP. The intended
  formula is E[⟨∇F,k⟩G] = E[F(W(k)G−⟨∇G,k⟩)]. Scalar/vector polynomial moments
  are already proved; this integral identity has not yet been formalized.
* Gradient closability needs this IBP identity plus density of an actual
  vector-valued polynomial test core. Scalar L² density alone is not a proof
  of either statement. The actual gradient is already representation
  independent, so no independently prescribed derivative data are needed.
* Divergence adjoints require a genuine densely defined vector-to-scalar
  operator, the adjoint pairing, and new graph-domain/spectral arguments.
  Neither graph-norm density nor full adjoint identification follows merely
  from this scalar Hilbert basis.
* The expected gradient weight Σ_α |α| |c_α|² and divergence coefficient
  Σᵢ√(αᵢ)u_{i,α−eᵢ} remain targets. The divergence domain must control the
  square-summability of the sum, allowing cancellation between coordinates.
* The original scalar cylindrical-density premise can now be replaced by an
  actual theorem on the standard finite product. Original D^{1,4} graph-core
  claims, closed Leibniz extensions, smooth nonpolynomial cylinders, Itô
  formulas, and infinite-dimensional limits still need new analytic proofs.

Verification: full `lake build`, `lake build Foundation.AxiomAudit`, and a fresh
`lake env lean Foundation/AxiomAudit.lean`. The 24 new public declarations are
explicitly queried, bringing the audit to 282 declarations. Dependencies are
only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom
axioms. Prior foundation proofs and original Lean/manuscript hashes are
checked unchanged. Only the two pre-existing unused-section-variable warnings
in `Foundation.Adjoint` remain; no new warnings or suppressed linters.

## Finite Gaussian gradient/divergence: dense closable polynomial operators (after 9fc7fbb)

This is a complete operator-core milestone: polynomial Gaussian IBP, genuine
scalar-to-vector gradient and vector-to-scalar divergence, both dense domains,
proved closability, closed extensions and adjoint inclusions, and actual tensor
Hermite lowering/raising. Full maximal-adjoint identification and spectral
domain characterizations are **not** claimed in this milestone.

The original `UnboundedCylindricalStructure` (`OperatorDerivative.lean:341–374`)
requires a cylindrical IBP formula and an extension from a purported graph core.
Its earlier `cyl_dense` field does not actually express convergence. The
manuscript's cylindrical reduction and Sobolev closure discussion likewise
needs analytic proofs. The new finite independent Gaussian model now supplies
a genuine polynomial IBP identity and closable operators. It does not establish
the original D^{1,4} graph-density or closed Leibniz extension claims. Original
sources and every previously verified foundation module remain unchanged.

### Spaces, domains, definitions, and sign convention

For every finite index type I, including the empty type, let μ = ∏ᵢ N(0,1) on
I → ℝ. The scalar Hilbert space is Hₛ = L²(μ;ℝ). The vector Hilbert space is
Hᵥ = L²(μ;EuclideanSpace ℝ I), with the Euclidean ℓ² fiber norm and inner
product, not the supremum norm on a plain Pi space.

Scalar and vector polynomial embeddings evaluate actual multivariate
polynomials, with all finite moments proved. Both embeddings are injective:
full support of μ converts equality a.e. of continuous polynomials into
equality everywhere, and polynomial extensionality gives equality of the
polynomials. Vector injectivity follows from the scalar coordinate maps.

The operator graphs are ranges of linear maps from actual polynomials:

    ∇₀[p] = [x ↦ (∂ᵢp(x))ᵢ],       dom(∇₀) = scalar polynomial embedding range;
    δ₀[u] = [Σᵢ(Xᵢuᵢ − ∂ᵢuᵢ)],  dom(δ₀) = vector polynomial embedding range.

Vertical uniqueness is proved from the injectivity of the input embeddings.
No derivative/output data are independently prescribed. The polynomial
vector used for ∇₀ is additionally verified to be the actual Fréchet gradient
on the Euclidean coordinate model. In particular δ₀ has the positive
Gaussian-adjoint sign convention, rather than the ordinary positive divergence.

The scalar polynomial domain is dense by the existing proved finite Gaussian
density theorem. Vector polynomial density is now proved separately:
orthogonality to fields with one polynomial component forces each scalar L²
component to vanish; the vector therefore vanishes a.e. Orthogonal-complement
theory gives density. There is no vector-density hypothesis and no assumption
about graph-norm density.

### Integration by parts, closability, and exact inclusions

`Foundation/FiniteGaussianIBP.lean` first proves the actual coordinate identity

    ∫ xᵢ p(x) dμ = ∫ ∂ᵢp(x) dμ.

Partial differentiation of a separable polynomial product differentiates
precisely its i-th factor. Finite-product Fubini and the previously verified
one-dimensional Stein identity prove the identity for every separable product.
Linearity and the already proved algebraic tensor Hermite spanning extend it
to every multivariate polynomial. Applying it to pq, with genuine product
integrability, gives

    ∫ (∂ᵢp)q dμ = ∫ p(Xᵢq−∂ᵢq) dμ.

Coordinate summation yields, for every scalar polynomial p and polynomial
vector field u,

    ⟨∇₀[p],[u]⟩_{Hᵥ} = ⟨[p],δ₀[u]⟩_{Hₛ}.

Both dense-domain hypotheses are proved independently. Mathlib's formal
adjoint theorem gives actual operator inclusions, including domains and values:

    ∇₀ ⊆ δ₀*,    δ₀ ⊆ ∇₀*.

The adjoints of these densely defined operators are closed. Their closed
extensions therefore prove closability of both polynomial operators. Their
actual graph closures, denoted `closedGradient` and `closedVectorDivergence`,
are closed, densely defined operators satisfying

    closure(∇₀) ⊆ δ₀*,    closure(δ₀) ⊆ ∇₀*.

Classical polynomial values are preserved on both closed graphs and for every
proof of polynomial domain membership. Polynomial domains are graph cores
for their own closures, by the definition and verified properties of graph
closure. This statement does NOT make them graph cores for the maximal
adjoints on the right. No equality between a closure and the opposite adjoint
has been inferred from scalar or vector L² density.

### Tensor actions and the outstanding spectral argument

`Foundation/FiniteGaussianLadders.lean` reuses the actual one-dimensional
polynomial operator graph actions to prove normalized polynomial lowering
and raising. These determine actual multivariate polynomial identities. For
e_α = ∏ᵢ H_{αᵢ}/√(αᵢ!) and eᵢ the coordinate unit multi-index:

    ∂ᵢe_α = √(αᵢ)e_{α−eᵢ} when αᵢ>0; ∂ᵢe_α = 0 when αᵢ=0;
    (Xᵢ−∂ᵢ)e_α = √(αᵢ+1)e_{α+eᵢ}.

These are proved for actual normalized polynomial representatives and their
operator L² graphs, not stipulated coefficient transformations. A vector
Hermite field with its sole nonzero component i equal to e_α belongs to δ₀'s
domain, and its output is exactly √(αᵢ+1)e_{α+eᵢ}. The corresponding tensor
scalar belongs to ∇₀'s domain, and each positive-degree gradient component
has the exact lowering weight above.

**Remaining unproved targets, not declaration meanings:** for scalar Hermite
coefficients c_α and vector-component coefficients u_{i,β}, the expected
closed-gradient criterion is

    Σ_α |α| |c_α|² < ∞,

and the expected maximal divergence criterion is square-summability of the
scalar sequence

    d_α = Σ_{i:αᵢ>0} √(αᵢ) u_{i,α−eᵢ}.

The divergence criterion controls the SQUARE OF THE SUM, allowing cancellation
between coordinates. Requiring each coordinate raising operator separately
to have finite weighted norm is generally stronger and is not used here. The
one-dimensional fact that derivative and divergence have the same domain
does not identify these different scalar/vector multivariate domains.

The next proof obligations are precise:

1. Derive and prove sufficient as well as necessary Hermite coefficient
   relations for both maximal adjoint graphs, using the complete scalar basis
   and a proved componentwise vector expansion/Parseval identity.
2. Prove square-summable coefficient realization in the required vector space,
   and the weighted norm formulas that characterize the scalar gradient.
3. Use **finite total-degree cutoffs** {|α|≤N}. Lowering changes total degree
   by −1; raising changes it by +1 for every coordinate. Thus the appropriate
   shifted output cutoff can retain all contributions to each divergence
   coefficient, including cancellations. Finiteness and both graph-limit
   convergence statements must be proved in Lean; they are not assumed.
4. Establish that these approximations are graph dense in δ₀* and ∇₀*, then
   deduce closure(∇₀)=δ₀* and closure(δ₀)=∇₀*. Until then only the displayed
   inclusions are established. Rectangular coordinate cutoffs must not be
   substituted without checking that boundary cancellations are preserved.

This is missing formalized spectral/approximation infrastructure, not a
counterexample to the finite Gaussian operator identifications. No infinite-
dimensional limit, Itô formula, or full Malliavin operator is claimed.

### Compatibility and correlated-coordinate limits

`gradientPolynomial_hasFDerivAt` proves that the computed Euclidean-valued
polynomial gradient represents the actual Fréchet derivative. It specializes
the existing genuine cylindrical derivative at the standard orthonormal basis.
All earlier arbitrary-family results remain preserved: for hᵢ in a finite real
Hilbert space, including linearly dependent vectors, the actual derivative is
Σᵢ ∂ᵢp(W(h))hᵢ and is independent of its polynomial cylinder representation.
These are geometric chain-rule statements and do not assert tensor
orthogonality for correlated coordinates.

The new Hilbert operators live on the independent product model. An
orthonormal change of ambient coordinates has the already proved
measure-preserving scalar polynomial pullback. Transporting the **closed**
vector operators and identifying their domains on an arbitrary ambient Hilbert
space requires a further vector L² transport theorem. A correlated or
rank-deficient family is not a measure-preserving identification with the full
independent product space; no such claim is made or used.

### Public declaration meanings and verification

All new names are in `OperatorDerivativeRewrite.Foundation.FiniteGaussian`.
The named `DecidableEq I` parameters on coordinate-update theorems are solely
computational decidability for finite-index updates, not analytic assumptions.

| Declarations | Mathematical meaning |
| --- | --- |
| `productPolynomialIntegral` | Integration as a linear functional on genuinely integrable polynomials |
| `polynomial_coordinate_eval`, `pderiv_coordinate_polynomial` | Genuine evaluation/substitution and coordinate polynomial differentiation |
| `tensorPolynomialMap_eval`, `tensorPolynomialMap_pderiv` | Product evaluation and differentiation of precisely one tensor factor |
| `productPolynomial_stein` | Multivariate coordinate Gaussian Stein identity |
| `coordinateDivergencePolynomial` | The actual expression Xᵢq−∂ᵢq |
| `productPolynomial_integration_by_parts` | Genuine integrable polynomial coordinate IBP |
| `ScalarGaussianL2`, `VectorGaussianL2` | The scalar and Euclidean-valued Gaussian L² Hilbert spaces |
| `productGaussian_openPos` | Proved full support of the independent product |
| `productPolynomialEmbedding_injective` | Uniqueness of actual scalar polynomial evaluation in L² |
| `vectorPolynomialFunction`, `vectorPolynomial_memLp` | Genuine Euclidean-valued polynomial functions with all finite moments |
| `vectorPolynomialL2`, `vectorPolynomialL2_coeFn` | Their actual L² classes and a.e. representatives |
| `vectorPolynomialEmbedding`, `vectorPolynomialEmbedding_injective` | Linear injective evaluation of actual polynomial fields |
| `vectorL2Component`, `vectorL2Component_coeFn`, `vectorPolynomialL2_component` | Genuine scalar L² coordinate projection and its polynomial compatibility |
| `vectorPolynomialL2_inner` | Proved decomposition of the vector Hilbert pairing into integrable component pairings |
| `eq_zero_of_vectorPolynomial_orthogonal`, `vectorPolynomialEmbedding_dense` | Independent proof of full vector polynomial L² density |
| `gradientPolynomial`, `divergencePolynomial` | Actual partial-derivative family and Σᵢ(Xᵢuᵢ−∂ᵢuᵢ) |
| `gradientPolynomialL2` | The actual Euclidean-valued polynomial gradient L² class |
| `productPolynomialL2_inner`, `gradient_divergence_polynomial_pairing` | Genuine scalar Hilbert pairing and full scalar/vector IBP |
| `polynomialGradientGraph`, `polynomialDivergenceGraph` | Linear ranges of genuine input/output polynomial evaluations |
| `polynomialGradientGraph_vertical_zero`, `polynomialDivergenceGraph_vertical_zero` | Proven single-valuedness of these graphs |
| `polynomialGradient`, `polynomialDivergence` | Genuine partial linear operators with exactly the polynomial domains |
| `polynomialGradient_graph`, `polynomialDivergence_graph` | Their graphs equal the proved single-valued polynomial graphs |
| `polynomialGradient_polynomial_graph`, `polynomialDivergence_polynomial_graph` | Actual polynomial input/output domain membership and values |
| `polynomialGradient_domain`, `polynomialDivergence_domain` | Exact algebraic scalar/vector polynomial domains |
| `polynomialGradient_dense_domain`, `polynomialDivergence_dense_domain` | Both domains are proved dense in their respective Hilbert spaces |
| `polynomialGradient_formalAdjoint` | IBP on the actual two operator domains |
| `polynomialGradient_le_divergence_adjoint`, `polynomialDivergence_le_gradient_adjoint` | ∇₀⊆δ₀* and δ₀⊆∇₀*, with domains and values |
| `polynomialGradient_isClosable`, `polynomialDivergence_isClosable` | Genuine closability from closed adjoint extensions |
| `closedGradient`, `closedVectorDivergence` | Actual graph closures of the polynomial operators |
| `closedGradient_isClosed`, `closedVectorDivergence_isClosed` | Proved closedness of those extensions |
| `closedGradient_dense_domain`, `closedVectorDivergence_dense_domain` | Their domains remain dense |
| `closedGradient_le_divergence_adjoint`, `closedVectorDivergence_le_gradient_adjoint` | The strongest closed-operator inclusions established here |
| `closedGradient_polynomial_graph`, `closedVectorDivergence_polynomial_graph` | Closed graphs preserve the classical polynomial values |
| `closedGradient_has_polynomial_core`, `closedVectorDivergence_has_polynomial_core` | Polynomial graph cores for their own closures, not for unproved maximal adjoint identifications |
| `gradientPolynomial_hasFDerivAt` | The computed gradient is the actual Euclidean Fréchet derivative |
| `closedGradient_polynomial_apply`, `closedVectorDivergence_polynomial_apply` | Actual polynomial values for every proof of closed-domain membership |
| `normalizedHermitePolynomial_derivative`, `normalizedHermitePolynomial_divergence` | Actual normalized one-dimensional polynomial ladder identities recovered from the verified operators |
| `tensorHermitePolynomial_lowering`, `tensorHermitePolynomial_lowering_zero` | Actual positive-degree lowering and zero-degree vanishing |
| `tensorPolynomialMap_coordinateDivergence`, `tensorHermitePolynomial_raising` | True separable-factor divergence and normalized tensor raising |
| `tensorHermiteVector`, `tensorHermiteVector_divergence_graph` | Actual one-component vector tensor field and its δ₀ graph action |
| `tensorHermite_gradient_graph`, `tensorHermite_gradient_component` | Actual ∇₀ tensor graph membership and normalized component lowering |

Verification consists of the full Lake build, the AxiomAudit target build,
and a fresh `lake env lean Foundation/AxiomAudit.lean`. All 73 new public
statements/definitions/instances are explicitly queried, for 355 audited
declarations in total. Only `propext`, `Classical.choice`, and `Quot.sound`
appear: no `sorryAx`, `admit`, or custom axioms. All prior foundation sources
and original Lean/manuscript hashes are checked unchanged. Only the two
pre-existing `Foundation.Adjoint` warnings remain; no new warnings or
suppressed linters.

## Finite Gaussian spectral domains and full adjoint identification (after a077fd6)

This milestone completes the finite independent Gaussian operator identification.
The earlier section describes the results at a077fd6; its outstanding spectral
and graph-core obligations are discharged here. The four new modules are
`FiniteGaussianSpectral`, `FiniteGaussianTruncation`, `FiniteGaussianAdjoints`,
and `FiniteGaussianDomains`. Original sources and all existing proof modules
remain unchanged. The root import and explicit axiom audit include the new work.

### Exact operator statements

For every finite index type I, set μ = ∏ᵢ N(0,1), Hₛ = L²(μ;ℝ), and
Hᵥ = L²(μ;EuclideanSpace ℝ I). These are the existing actual L² spaces and
polynomial operators, with the previously proved Gaussian integration by parts.
Write eα for the complete normalized tensor Hermite basis, and define

    cα(f) = ⟨eα,f⟩,
    uᵢ,α = ⟨eα, componentᵢ(u)⟩,
    aᵢ,α(f) = √(αᵢ+1) cα+eᵢ(f),
    bβ(u) = Σᵢ:βᵢ>0 √βᵢ uᵢ,β−eᵢ,
    |α| = Σᵢ αᵢ.

`Function.update` raises or lowers the indicated coordinate and retains every
other coordinate. All coefficients come from the actual L² input, not from
independently supplied derivative data. `DecidableEq I`, when present in a
coordinate-update statement, is an implementation requirement for finite index
operations, not a regularity or graph-density assumption. Statements whose
types do not need it omit it and use local classical decidability in proofs.

The verified exact closed graph and domain statements are:

- `closedGradient_graph_iff`: (f,g) belongs to closure(∇₀)'s graph iff
  uᵢ,α(g) = aᵢ,α(f) for every i and α.
- `closedGradient_domain_iff`: f belongs to closure(∇₀)'s domain iff
  Σα |α| |cα(f)|² is summable (equivalently finite, since terms are nonnegative).
- `closedVectorDivergence_graph_iff`: (u,g) belongs to closure(δ₀)'s graph iff
  cβ(g) = bβ(u) for every β.
- `closedVectorDivergence_domain_iff`: u belongs to closure(δ₀)'s domain iff
  Σβ |bβ(u)|² is summable. No individual component derivative domain is required.
- `closedVectorDivergence_norm_sq`: its output satisfies
  ‖g‖² = Σβ |bβ(u)|².
- `closedGradient_eq_divergence_adjoint`: closure(∇₀) = δ₀*.
- `closedVectorDivergence_eq_gradient_adjoint`: closure(δ₀) = ∇₀*.
- The two closed operators are also mutual adjoints, via the proved invariance
  of adjoints under closure of a densely defined closable operator.

The vector divergence condition combines coordinates **before squaring**.
Replacing it by Σᵢ,α (αᵢ+1)|uᵢ,α|² < ∞ would discard legitimate cancellations.
The proofs never use that stronger condition. Square summability of b is proved
sufficient by scalar coefficient realization and the whole polynomial adjoint
identity, then by actual polynomial graph approximation. It is not assumed as
proof of any componentwise integrability or domain membership.

### Noncircular realization and proof dependencies

1. The previously verified one-dimensional Hermite completeness and noncircular
   multivariate polynomial density supply `tensorHermiteBasis` and algebraic
   `tensorHermitePolynomial_span`.
2. Parseval follows from Mathlib's ℓ² norm theorem applied to that Hilbert basis.
   Its inverse representation realizes every square-summable real coefficient
   family as an actual scalar Gaussian L² class.
3. `tensorHermite_gradient_pairing` uses the already verified genuine partial
   derivatives and lowering identities to compute bβ for any vector L² input.
   Testing the adjoint equation on these polynomial tensors proves necessity.
4. Sufficiency for ∇₀* is proved by a linear pairing functional on actual
   multivariate polynomials. Its kernel contains every Hermite tensor polynomial;
   algebraic spanning proves the adjoint equation on the entire polynomial
   gradient domain. This does not assume maximal-domain membership or graph density.
5. Continuous coordinate insertions reconstruct every vector L² class from its
   actual scalar components. They also realize square-summable component
   coefficient families as genuine vector L² classes.
6. Raising a coordinate is an injective map onto the positive-coordinate modes.
   The coordinate weighted series vanishes on the complement of that image.
   Mathlib's injective summability reindexing proves the exact coordinate weight,
   and a finite sum of nonnegative coordinate weights gives |α|. This proves
   both directions of the scalar weighted-domain statement, with output graph
   membership established by the true polynomial approximants.

### Actual total-degree graph approximants

`hermiteDegreeCutoff N` is the finite set {|α| ≤ N}. It is constructed inside a
finite coordinate box and filtered by total degree. Its exact membership theorem
and cofinality in the finite-subset filter are proved, not assumed. Scalar
truncation P_N f is Σ|α|≤N cα(f)eα; vector truncation P_N u applies this same
projection in every component. Both are explicitly evaluated polynomial classes
and converge in their respective actual L² spaces by completeness and continuous
coordinate insertion.

The verified graph approximants are:

    (P_(N+1) f, P_N g) ∈ graph(∇₀)  for every (f,g) ∈ graph(δ₀*),
    (P_N u, P_(N+1) g) ∈ graph(δ₀)  for every (u,g) ∈ graph(∇₀*).

For divergence output index β, every nonzero summand uses input degree |β|−1.
Consequently all coordinates contributing to bβ survive the cutoff together:

    bβ(P_N u) = 1_{|β|≤N+1} bβ(u).

This is the proved `divergenceCoefficient_truncation`, and it is the exact lemma
that protects cancellation. The complementary lowering projection identity is
proved for gradient coefficients. The graph membership of each approximation
comes from the original polynomial operator; equality of its output with the
projected adjoint output is established by coefficient completeness.

Both approximation pairs converge in the product L² topology. Additionally,
`gradient_adjoint_truncation_graphNorm_tendsto` and
`divergence_adjoint_truncation_graphNorm_tendsto` prove explicitly that the
squared Hilbert graph error, ‖input error‖² + ‖output error‖², tends to zero.
Actual graph closure then yields each reverse adjoint inclusion. The two
identifications have separate approximation proofs; neither is inferred merely
from the formal adjoint inclusion or L² polynomial density. Polynomial graph
cores for the full maximal adjoints follow only after these equalities.

### Zero dimension, classical values, and cylindrical compatibility

For an empty index type, |α|=0 and the cutoff is the sole vacuum index for every N.
Scalar and vector projections are the identity. The closed gradient domain is
all Hₛ and its value is the unique zero vector. The closed divergence domain is
all Hᵥ and its value is zero in Hₛ. These are explicit Lean theorems, not an
implicit restriction to positive dimensions. All domain and graph theorems also
work for arbitrary finite dimension, in particular `Fin n` for every n.

The definitions of ∇₀, δ₀, and their closures have not changed. Existing
`closedGradient_polynomial_apply` and `closedVectorDivergence_polynomial_apply`
therefore retain the actual classical values ∂ᵢp and Σᵢ(Xᵢuᵢ−∂ᵢuᵢ). Their
previous axiom queries are rerun together with the new identifications.
`gradientPolynomial_hasFDerivAt` still identifies the gradient as the actual
Fréchet gradient on the Euclidean coordinate model. Earlier orthonormal-coordinate
pullback compatibility and correlated-cylinder representation independence,
product rules, and integrability proofs are preserved unchanged.

Tensor orthogonality and these coefficient formulas apply to the independent
standard-coordinate model. They do not assert tensor orthogonality for an
arbitrary correlated or linearly dependent coordinate family. Transport of full
closed scalar/vector operators to an arbitrary finite Hilbert Gaussian model,
and an explicit transformation of maximal domains for redundant correlated
representations, remain separate obligations. No infinite-dimensional limit,
infinite-dimensional cylindrical graph density, smooth nonpolynomial core,
D^{1,4} multiplier graph density, closed Leibniz extension, or Itô formula is
claimed here. There is no remaining analytic gap in the stated finite independent
Gaussian adjoint identifications or spectral domain criteria.

### Declaration meanings

All 80 new public definitions and theorems are explicitly queried by the axiom
audit. Each is covered below; supporting statements are recorded to make the
proof scope reviewable.

| Declarations | Precise meaning |
| --- | --- |
| `scalarHermiteCoefficient`, `vectorHermiteCoefficient` | Actual scalar tensor coefficients and component coefficients of a vector L² class |
| `gradientCoefficient`, `divergenceCoefficient` | Actual spectral lowering formula and combined raising formula |
| `scalarHermiteCoefficient_hasSum_sq` | Parseval with the scalar L² norm |
| `exists_scalarHermite_coefficients`, `scalarHermiteCoefficient_ext` | Genuine scalar coefficient realization and uniqueness |
| `tensorHermite_gradient_component_zero`, `tensorHermite_gradient_pairing` | Genuine zero-mode vanishing and gradient pairing with an arbitrary L² field |
| `gradient_adjoint_coefficients`, `gradient_adjoint_graph_of_coefficients`, `gradient_adjoint_graph_iff` | Necessary and sufficient combined coefficients for the full graph of ∇₀* |
| `gradient_adjoint_domain_iff`, `gradient_adjoint_norm_sq` | Exact maximal divergence domain and output norm |
| `closedGradient_adjoint_eq`, `closedVectorDivergence_adjoint_eq` | Adjoints of the closures equal the corresponding polynomial adjoints |
| `closedVectorDivergence_coefficients`, `polynomialDivergence_coefficients` | Combined coefficients for the existing closed and classical polynomial divergence values |
| `divergenceCoefficient_empty`, `gradient_adjoint_domain_empty`, `gradient_adjoint_graph_empty` | Zero coefficients and full zero-valued maximal divergence in dimension zero |
| `hermiteDegree`, `hermiteDegreeCutoff` | Total multi-index degree and its actual finite cutoff |
| `mem_hermiteDegreeCutoff`, `hermiteDegreeCutoff_tendsto` | Exact cutoff membership and exhaustion of the finite-subset filter |
| `scalarHermiteTruncationPolynomial`, `scalarHermiteTruncation` | Genuine polynomial representative and its scalar Hermite projection |
| `scalarHermiteTruncationPolynomial_L2`, `scalarHermiteTruncation_coefficient`, `scalarHermiteTruncation_tendsto` | Actual polynomial membership, exact cutoff coefficients, and unconditional L² convergence |
| `vectorL2Insert`, `vectorL2Insert_polynomial`, `vectorL2_reassemble` | Continuous coordinate insertion, genuine polynomial compatibility, and exact reconstruction of any vector L² class |
| `vectorHermiteTruncationPolynomial`, `vectorHermiteTruncation` | Genuine polynomial vector representative and its common total-degree projection |
| `vectorHermiteTruncation_component`, `vectorHermiteTruncation_coefficient`, `vectorHermiteTruncation_tendsto` | Exact component projections and coefficients, with vector L² convergence |
| `hermiteDegree_lower`, `hermiteDegree_raise` | Coordinate lowering/raising changes total degree by exactly one |
| `divergenceCoefficient_truncation`, `gradientCoefficient_truncation` | Exact shifted spectral projections; divergence cancellations are retained |
| `gradient_adjoint_truncation_graph`, `gradient_adjoint_truncation_tendsto` | Genuine polynomial divergence graph approximants of every ∇₀* pair and their convergence |
| `closedVectorDivergence_graph_of_coefficients` | Combined coefficient realization in the actual polynomial divergence graph closure |
| `closedVectorDivergence_eq_gradient_adjoint`, `closedVectorDivergence_domain_iff` | Full divergence adjoint identification and its exact combined square-sum domain |
| `tensorHermiteVector_inner`, `divergence_adjoint_coefficients` | Actual vector tensor coefficient pairing and necessary coefficients of the full δ₀* graph |
| `vectorHermiteCoefficient_ext` | Uniqueness of vector L² classes from their component tensor coefficients |
| `divergence_adjoint_truncation_graph`, `divergence_adjoint_truncation_tendsto` | Genuine polynomial gradient graph approximants of every δ₀* pair and their convergence |
| `closedGradient_graph_of_adjoint`, `closedGradient_eq_divergence_adjoint` | Reverse gradient graph inclusion and full gradient adjoint identification |
| `closedGradient_eq_closedVectorDivergence_adjoint`, `closedVectorDivergence_eq_closedGradient_adjoint` | Mutual adjoint identities for the closed operators |
| `divergence_adjoint_has_polynomial_core`, `gradient_adjoint_has_polynomial_core` | Polynomial graph cores of the actual full maximal adjoints |
| `vectorL2Component_insert`, `exists_vectorHermite_coefficients` | Exact coordinate insertion/projection and genuine vector coefficient realization |
| `gradient_coefficients_truncation_graph`, `closedGradient_graph_of_coefficients`, `closedGradient_graph_iff` | Genuine gradient graph construction from coefficients and exact closed gradient graph |
| `hermiteRaise_injective`, `mem_range_hermiteRaise`, `gradientCoefficient_summable_iff` | Noncircular reindexing of positive-coordinate modes into the exact coordinate weight |
| `hermiteDegree_weight_summable_iff`, `closedGradient_domain_iff` | Finite-sum equivalence of coordinate and total weights, then the exact scalar gradient domain |
| `closedGradient_domain_empty`, `closedGradient_graph_empty` | Full zero-dimensional scalar domain and actual zero gradient |
| `closedVectorDivergence_graph_iff`, `closedVectorDivergence_norm_sq` | Exact closed divergence graph and combined output norm |
| `closedVectorDivergence_graph_empty`, `closedVectorDivergence_domain_empty` | Actual zero divergence and full vector domain in zero dimensions |
| `divergence_adjoint_graph_iff` | Exact coefficient characterization of the full maximal gradient δ₀* |
| `divergence_adjoint_truncation_graphNorm_tendsto`, `gradient_adjoint_truncation_graphNorm_tendsto` | Explicit squared Hilbert graph-error convergence for both total-degree approximation schemes |
| `hermiteDegreeCutoff_empty`, `scalarHermiteTruncation_empty`, `vectorHermiteTruncation_empty` | Sole vacuum cutoff and identity projections in dimension zero |

Verification completed successfully: full `lake build` (3219 jobs),
`lake build Foundation.AxiomAudit` (3218 jobs), and a fresh
`lake env lean Foundation/AxiomAudit.lean`. The fresh output contains exactly
435 declarations (355 existing plus 80 new). Its only axiomatic dependencies
are `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or
custom axiom. The complete raw output is saved at
`.lake/build/finite-gaussian-spectral-axioms.log` (ignored build artifact).
Only the two pre-existing `Foundation.Adjoint` section-variable warnings remain;
all four new modules compile without warnings or suppressed linters.
Every pre-existing proof module except the extended axiom query file is
unchanged from a077fd6. SHA-256 verification confirms both original sources
are unchanged. No theorem statement was weakened and no environment dependency
or toolchain was changed.

## Countable Gaussian probability space and first-chaos L² extension (after 9330547)

This milestone constructs an actual probability space of countably many independent
standard Gaussian coordinates and a genuine L² extension of their finite linear
combinations. It does **not** complete an isonormal Gaussian process: Gaussianity
of every infinite-series limit is still a separate analytic obligation.

The sample space is Ω = ℝ^ℕ with its product measurable space and probability
measure μ = infinitePi (n ↦ gaussianReal 0 1). It is not ℓ² and is not an
identity-covariance Gaussian Radon measure on an infinite-dimensional Hilbert
space. The coefficient Hilbert space ℓ² is distinct from this sample space.
No assertion that sample sequences are square summable is used.

### Exact definitions and verified declarations

All names below are in `OperatorDerivativeRewrite.Foundation.InfiniteGaussian`.
The two source modules introduce only the following declarations:

| Declaration | Precise mathematical meaning |
| --- | --- |
| `SampleSpace` | Real sequences ℕ → ℝ, equipped with the existing product measurable space. |
| `gaussianProduct` | Mathlib's countable product of the verified standard real Gaussian measure. |
| `gaussianProduct_probability` | This product measure has total mass one. |
| `GaussianL2` | The actual real L² space of this probability measure. |
| `coordinate` | Evaluation Xₙ(ω) = ωₙ. |
| `coordinate_measurePreserving` | Xₙ pushes μ forward to the standard real Gaussian measure. |
| `coordinate_law` | Exact equality μ.map Xₙ = gaussianReal 0 1. |
| `coordinate_hasGaussianLaw` | Each actual evaluation variable has Gaussian law. |
| `coordinates_independent` | The entire coordinate family is jointly independent in Mathlib's `iIndepFun` sense. |
| `coordinate_memLp` | Xₙ belongs to every finite Lp, including the exponent-zero convention of Mathlib. |
| `finiteProjection` | Restriction ω ↦ (ωᵢ)ᵢ∈s for any finite set s of natural indices. |
| `finiteProjection_measurePreserving` | Its law is the previously verified finite independent product Gaussian, also when s is empty. |
| `finitePullback` | An actual linear isometry L²(ℝˢ, γˢ) → L²(Ω, μ) by composition with restriction. |
| `finitePullback_coeFn` | Its representative agrees almost everywhere with the composed finite-dimensional representative. |
| `finitePullback_inner` | It preserves every real Hilbert inner product. |
| `polynomialCylinder` | The actual random variable p((ωᵢ)ᵢ∈s), for a genuine multivariate polynomial p. |
| `polynomialCylinder_memLp` | Each such random variable has all finite moments, transported from the verified finite marginal. |
| `polynomialCylinderEmbedding` | Linear embedding of these evaluated polynomials into L²(Ω, μ). |
| `polynomialCylinderEmbedding_coeFn` | The embedded class is represented almost everywhere by the actual polynomial evaluation. |
| `polynomialCylinderEmbedding_injective` | For fixed s, distinct polynomials give distinct L² classes. |
| `finiteHermite_orthonormal` | For each fixed s, the pullback of its complete finite tensor Hermite family remains orthonormal. Completeness in the entire infinite product is not asserted. |
| `coordinateL2` | L² class of the actual evaluation Xₙ, built using its proved integrability. |
| `coordinateL2_coeFn` | This class has the stated actual evaluation representative almost everywhere. |
| `coordinate_integral` | E[Xₙ] = 0. |
| `coordinate_product_integral` | E[Xₙ Xₘ] = 1 if n = m and 0 otherwise. |
| `coordinateL2_orthonormal` | The coordinate L² classes form an orthonormal family. No completeness in all L² is claimed. |
| `CoefficientSpace` | Mathlib's Hilbert space lp (n ↦ ℝ) 2, namely real ℓ² coefficients. |
| `firstChaosEmbedding` | The linear isometry from ℓ² into L² constructed by the orthogonal Hilbert-sum theorem applied to the proved coordinate orthonormal family. |
| `firstChaos_hasSum` | For every h ∈ ℓ², the finite sums of hₙ Xₙ converge unconditionally in L² to `firstChaosEmbedding h`. |
| `firstChaos_single` | The image of a single coefficient a at index n is exactly a times the actual coordinate class. |
| `firstChaos_inner` | ⟨W h, W k⟩L² = ⟨h, k⟩ℓ². This is stated as an L² inner product; centering of every infinite limit is not silently assumed. |
| `firstChaos_norm` | ‖W h‖L² = ‖h‖ℓ². |
| `firstChaos_finiteSum` | The extension agrees with every finite linear combination of actual coordinate classes. |
| `firstChaos_injective` | Different ℓ² coefficient vectors yield different L² random variables. |

### Proof dependencies and absence of circular assumptions

The measure and marginal proofs reuse `Measure.infinitePi`, its probability
instance, `measurePreserving_eval_infinitePi`, `infinitePi_map_restrict`, and
`iIndepFun_infinitePi`. They do not posit an infinite Gaussian measure axiom.
Polynomial integrability is pulled back from the existing proved finite-dimensional
`productPolynomial_memLp`; faithfulness uses the existing polynomial embedding
injectivity and Mathlib's isometric Lp pullback. Tensor orthogonality is used only
for independent coordinate marginals and only within a fixed finite index set.

The coordinate second moment is derived from the previously verified real
polynomial Stein identity applied to p(x) = x. Off-diagonal products use genuine
coordinate independence and proved L² membership. The resulting orthonormality
is the input to Mathlib's `OrthogonalFamily.linearIsometry`, whose
`hasSum_linearIsometry` proves actual unconditional L² convergence. There is
no assumed convergence, no independently prescribed derivative, and no assumed
infinite-dimensional graph domain or adjoint identification.

Finite projections include s = ∅ without special hypotheses. Earlier correlated
finite-dimensional coordinates and their true polynomial derivatives are
preserved unchanged; this new independent sequence model does not assert tensor
orthogonality for correlated coordinates. Passing from independent sequence
coordinates to correlated ℓ² combinations requires the Gaussian limit result
below before claiming an isonormal family.

### Remaining analytic obligations and next task

The single best next task is to prove, for every h ∈ ℓ², that the actual
representative of `firstChaosEmbedding h` has law N(0, ‖h‖²). A noncircular
route is to prove the exact Gaussian law of finite weighted coordinate sums,
transport their proved L² convergence to convergence in probability/distribution,
and identify the limiting characteristic function while variances tend to
‖h‖². The current unconditional L² convergence theorem is a proved prerequisite,
not a hypothesis substituting for Gaussianity. Centering and joint Gaussianity
of all finite families of these limits must also be established to complete the
isonormal process and correlated-coordinate model.

Additional obligations before infinite-dimensional Malliavin operators are:

- Density of the union of finite-coordinate polynomial spaces in L²(Ω, μ).
  Finite-dimensional polynomial density alone does not establish this; one needs
  density of finite-coordinate measurable cylinders or a proved conditional
  expectation approximation. Pulled-back finite Hermite families overlap as s
  changes, so their union cannot simply be declared an orthonormal basis.
- Compatibility under enlargement and renaming of finite coordinate sets,
  including representation independence of the resulting Hilbert-valued
  polynomial derivative. The fixed-set polynomial injectivity proved here does
  not by itself settle comparisons between different coordinate sets.
- A genuine ℓ²-valued cylindrical gradient with proved L² integrability,
  Gaussian integration by parts, dense domain, and closability.
- The divergence adjoint, graph cores, and any infinite-dimensional spectral
  domain characterization. The finite-dimensional equalities are not imported
  as infinite-dimensional operator equalities.

No infinite-dimensional derivative, divergence, Itô formula, or full isonormal
Gaussian law is claimed in this milestone.

### Verification

The complete `lake build` succeeds (3292 jobs). Both new modules compile without
new warnings; the two existing unused-section-variable warnings in
`Foundation/Adjoint.lean` remain unchanged. A fresh direct Lean run of
`Foundation/AxiomAudit.lean` yields 469 results for 469 explicit queries,
including all 34 new declarations. The only dependencies reported are
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom is
reported. The fresh raw output is in the ignored build artifact
`.lake/build/infinite-gaussian-foundation-axioms.log`.

All earlier proof modules are unchanged. The original `OperatorDerivative.lean`
and `OperatorDerivative.tex` retain their previously recorded SHA-256 hashes.

## Genuine ℓ² isonormal Gaussian process (after aceed38)

The Gaussian law obligation left by the preceding milestone is now proved for
the original `firstChaosEmbedding`, without changing that construction or any
earlier proof module. On Ω = ℝ^ℕ with the countable product standard Gaussian
probability measure μ, the existing linear isometry W : ℓ² → L²(Ω, μ) satisfies

- μ.map W(h) = N(0, ‖h‖²) for every h ∈ ℓ², including h = 0;
- E[W(h)] = 0, E[W(h)W(k)] = Cov(W(h),W(k)) = ⟨h,k⟩;
- every finite family (W(hᵢ)) is jointly Gaussian, even when its Gram matrix is
  singular or coordinates coincide;
- linearity holds exactly as an L² linear map and almost everywhere for each
  fixed finite linear relation between actual representatives.

`firstChaos_isGaussianProcess` verifies Mathlib's Gaussian process predicate for
these actual representatives indexed by all ℓ² vectors. Together with the
proved linear isometry and covariance theorem, this establishes a genuine real
isonormal Gaussian process over ℓ². There is no assumption of Gaussianity of an
L² limit and no assumed joint Gaussianity.

### Exact new definitions and theorems

All names are in `OperatorDerivativeRewrite.Foundation.InfiniteGaussian`.
The complete list of 30 new declarations is:

| Declaration | Precise mathematical content |
| --- | --- |
| `weightedSum` | The actual finite random variable Sₛ(a)(ω) = Σₙ∈s aₙωₙ. |
| `weightedSumL2` | Its L² class, constructed as the finite sum of proved coordinate classes. |
| `weightedSumL2_coeFn` | That L² class is represented almost everywhere by Sₛ(a). |
| `weightedSum_charFun` | Its characteristic function at t is exp(−t² Σₙ∈s aₙ²/2). |
| `weightedSum_law` | Its exact law is N(0, Σₙ∈s aₙ²), also for empty sums and zero coefficients. |
| `weightedSumL2_tendsto` | Initial-segment weighted sums converge to the original W(h) in L². |
| `weightedSumL2_tendstoInMeasure` | These actual L² representatives converge to W(h) in probability. |
| `weightedSumL2_tendstoInDistribution` | They converge to W(h) in distribution under μ. |
| `coefficientSquares_hasSum` | Σₙ hₙ² converges unconditionally to ‖h‖ℓ²². |
| `firstChaos_charFun` | The actual limit law has characteristic function exp(−‖h‖²t²/2). |
| `firstChaos_law` | Equality of the actual pushforward measure with N(0, ‖h‖²), without a nonzero-norm restriction. |
| `firstChaos_hasGaussianLaw` | Gaussianity of the actual representative of W(h). |
| `firstChaos_integral` | E[W(h)] = 0 for every h. |
| `firstChaos_product_integral` | E[W(h)W(k)] = ⟨h,k⟩ℓ². |
| `firstChaos_covariance` | Cov(W(h),W(k)) = ⟨h,k⟩ℓ², for arbitrary h and k. |
| `firstChaos_zero_law` | W(0) has the point-mass law δ₀. |
| `firstChaos_add_ae` | W(h+k) = W(h)+W(k) almost everywhere for each h,k. |
| `firstChaos_smul_ae` | W(ah) = aW(h) almost everywhere for each a,h. |
| `firstChaosFamily` | The actual finite random vector ω ↦ (W(hᵢ)(ω))ᵢ. This definition has no prescribed Gaussianity field. |
| `firstChaos_linearCombination_ae` | W(Σᵢ aᵢhᵢ) = Σᵢ aᵢW(hᵢ) almost everywhere. |
| `firstChaosFamily_linear_ae` | For each continuous real linear form L on the finite coordinate space, L(W(hᵢ)) agrees almost everywhere with W(Σᵢ L(eᵢ)hᵢ). |
| `firstChaosFamily_linear_law` | The exact law of that projection is N(0, ‖Σᵢ L(eᵢ)hᵢ‖²). |
| `firstChaosFamily_hasGaussianLaw` | Joint Gaussianity for every finite index type and arbitrary vectors hᵢ. Uses `Finite`, with an enumeration chosen only inside the proof. |
| `firstChaosFamily_covariance` | The covariance matrix of the finite random vector is its Gram matrix (⟨hᵢ,hⱼ⟩). The individual covariance equality does not require finiteness. |
| `firstChaos_unit` | W(eₙ) is exactly the original coordinate L² class. |
| `firstChaosFamily_unit_law` | Every finite family of unit coefficients has exactly the original finite product Gaussian marginal law, including the empty family. |
| `firstChaos_variance` | Var(W(h)) = ‖h‖². |
| `firstChaos_finiteSupport_ae` | W of a finite-support coefficient vector is the actual finite weighted coordinate sum almost everywhere. |
| `firstChaosFamily_finiteCoordinates_law` | A finite coefficient matrix A supported in a finite coordinate set s yields exactly the pushforward of the previously verified finite product Gaussian γˢ by x ↦ Ax. No invertibility or independence of output rows is required. |
| `firstChaos_isGaussianProcess` | Mathlib's `IsGaussianProcess` holds for the actual process indexed by all ℓ² vectors. |

### Noncircular limiting argument

The finite characteristic function calculation uses the previously verified
standard Gaussian evaluation laws and joint independence from the product
measure. Measurable coordinate scaling preserves independence. The genuine
one-dimensional theorem `GaussianCore.W_gaussian_law` supplies the scaled
coordinate laws; Mathlib's characteristic function product formula for independent
finite sums then proves exp(−t²Σ aₙ²/2). Uniqueness of finite measure
characteristic functions proves the finite-sum law as well.

The prior unconditional L² series theorem gives convergence of initial-segment
sums. `tendstoInMeasure_of_tendsto_Lp` explicitly proves convergence in
probability. `TendstoInMeasure.tendstoInDistribution_of_aemeasurable` then proves
convergence in distribution of the measurable representatives. Mathlib's
`TendstoInDistribution.tendsto_charFun` yields convergence to the characteristic
function of the actual limit law. These are separate proved implications;
L² convergence is not treated as the conclusion about laws.

Mathlib's `lp.hasSum_norm`, specialized to exponent two, proves Σ hₙ² = ‖h‖².
Continuity of real-to-complex coercion, scalar arithmetic and complex exponential
therefore identifies the pointwise characteristic function limit. Uniqueness of
limits equates this function with the characteristic function of W(h).
`Measure.ext_of_charFun` gives the exact centered Gaussian measure equality.
No division by ‖h‖ occurs, so the zero vector is covered by the same argument
and is explicitly identified with δ₀.

Joint Gaussianity is derived after all scalar laws are proved. Every continuous
linear form on a finite real coordinate space is expanded in coordinate unit
vectors. Exact L² linearity, plus the verified almost-everywhere representatives
of finite sums and scalar multiples, identifies its evaluation on the finite
family with an actual W of the corresponding ℓ² combination. Its scalar law is
already known. `isGaussian_of_map_eq_gaussianReal` then proves that the joint
pushforward measure is Gaussian. This requires no orthogonality, independence,
positive-definite covariance, or graph-domain hypothesis. All finite dimensions,
including dimension zero, are covered by the finite-index statements.

Centering follows by integration against the proved Gaussian law. Product
expectations reuse the original Hilbert isometry and the definition of the L²
inner product; the product is integrable by the existing L² inner-product
infrastructure. The covariance and variance identities then use the proved
centering and Mathlib's covariance/variance formulas. Joint Gaussianity is not
used to manufacture covariance or to assume an L² multiplication closure.

### Compatibility and scope

The original coordinate classes and finite Hermite, polynomial, derivative,
divergence, graph-domain and adjoint proofs are unchanged. Unit vectors in ℓ²
recover their exact coordinate classes and finite product laws. More generally,
finite-support coefficient matrices recover actual correlated and dependent
linear coordinate families as pushforwards of the same finite product Gaussian.
Tensor orthogonality continues to apply to the independent input coordinates;
it is not asserted for the correlated output coordinates.

The process is defined over the real coefficient Hilbert space ℓ². Its sample
space remains ℝ^ℕ with product measure; no identity-covariance Gaussian Radon
measure on ℓ² is claimed. Linearity of representatives is proved almost
everywhere for each fixed relation, not as a simultaneous pointwise linear
functional on all of ℓ² outside one universal null set.

The Gaussian-law, centering, joint-Gaussianity and correlated-coordinate
obligations listed in the previous milestone are resolved. Before constructing
infinite-dimensional cylindrical derivatives, the remaining requirements are:

- proved density of finite-coordinate polynomial cylinders in the full product
  Gaussian L² space (finite-dimensional density alone does not prove this);
- a genuine Hilbert-valued derivative determined by actual finite polynomial
  or smooth functions, with representation independence across finite Gaussian
  families and appropriate integrability;
- Gaussian integration by parts, a dense derivative domain, and closability;
- identification of the divergence adjoint and any claimed infinite-dimensional
  graph cores or spectral domains;
- if needed, transport from ℓ² to other separable real Hilbert index spaces
  through a chosen Hilbert-space isometry, with its compatibility proved.

No infinite-dimensional derivative, divergence, graph-domain identity, or Itô
formula is introduced in this milestone.

### Verification of the complete isonormal milestone

The full `lake build` succeeds (3345 jobs). Both new proof modules compile
without warnings; the two older unused-section-variable warnings in
`Foundation/Adjoint.lean` remain unchanged. A fresh direct Lean run of
`Foundation/AxiomAudit.lean` returns 499 results for 499 explicit axiom queries,
including all 30 new declarations. Its complete dependency set is
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx` or custom
axioms. Raw output is retained as the ignored build artifact
`.lake/build/infinite-gaussian-isonormal-axioms.log`.

The original source SHA-256 hashes still match the recorded baseline. All earlier
proof modules, dependency configuration, lockfile, and Lean toolchain are
unchanged. The root imports and audit module are extended to include the two
new verified modules.

## Full product L² polynomial cylinder density (after c1202d0)

This is the first complete milestone toward the requested infinite-dimensional
Malliavin derivative. It resolves polynomial cylinder density in the entire
countable Gaussian product L² space. It does not yet construct that derivative,
its closed extension, or a divergence operator.

### Exact core and verified declarations

`MvPolynomial ℕ ℝ` is an algebraic polynomial space: each polynomial involves
only finitely many variables. The existing sample space Ω = ℝ^ℕ and measure μ
are preserved. The new evaluation map sends p to the actual L² class of
ω ↦ p(ω), with integrability established before this class is constructed.
Its range is exactly the union of the existing finite-coordinate polynomial
spaces, not an assumed closure or merely a larger linear span.

All fourteen new declarations are in
`OperatorDerivativeRewrite.Foundation.InfiniteGaussian`:

| Declaration | Exact meaning |
| --- | --- |
| `coordinatePolynomial_memLp` | Actual evaluation of every p ∈ ℝ[ℕ] belongs to all finite Lp spaces. This is proved by finite-variable renaming and the verified finite marginal estimates. |
| `coordinatePolynomialL2` | The actual L² equivalence class of ω ↦ p(ω). |
| `coordinatePolynomialL2_coeFn` | Its representative agrees almost everywhere with actual evaluation. |
| `coordinatePolynomialEmbedding` | Linear evaluation map ℝ[ℕ] → L²(Ω, μ); its image is the algebraic coordinate polynomial core. |
| `coordinatePolynomialL2_rename` | Renaming a finite-index polynomial into natural-number variables gives exactly its existing finite-cylinder L² class. |
| `coordinatePolynomialEmbedding_range` | The image is exactly ⋃ₛ range(polynomialCylinderEmbedding s), over all finite sets s ⊆ ℕ. |
| `coordinatePolynomialEmbedding_injective` | Distinct algebraic coordinate polynomials give distinct L² classes. Two polynomials are first placed in one common finite variable set, where existing injectivity applies. |
| `ae_zero_of_cylinder_integrals` | An integrable real function whose integrals vanish on every finite measurable cylinder is zero almost everywhere; product sigma-algebra generation is proved infrastructure, not an assumption of cylinder density. |
| `orthogonal_finitePullback` | Orthogonality to every coordinate polynomial implies orthogonality to every L² class pulled back from any finite Gaussian marginal. |
| `orthogonal_cylinder_integral` | Such an orthogonal L² function has zero integral on every finite measurable cylinder. |
| `eq_zero_of_coordinatePolynomial_orthogonal` | The orthogonal complement of the algebraic coordinate polynomial core is trivial. |
| `coordinatePolynomialEmbedding_dense` | The image of the actual polynomial evaluation map is dense in the whole product Gaussian L² space. |
| `polynomialCylinders_dense` | Equivalently, the actual union of finite-coordinate polynomial spaces is dense in the whole L² space. |
| `exists_polynomialCylinder_approx` | For every f ∈ L² and ε > 0, there are a finite set s and a genuine polynomial p ∈ ℝ[s] with ‖f − polynomialCylinderEmbedding s p‖L² < ε. |

### Noncircular density proof

Every countable-variable polynomial is renamed from a finite variable set using
Mathlib's `MvPolynomial.exists_finset_rename`. Its integrability and finite
pullback identification therefore reuse the already verified finite-dimensional
results. `exists_finset_rename₂` puts two polynomials in one common finite set,
which proves injectivity without any infinite-dimensional support assumption.
These are actual finite polynomial cylinders, including constants and the
empty coordinate set.

For density, take an arbitrary f ∈ L² orthogonal to all these polynomial classes.
For each fixed finite coordinate set s, the continuous functional
 g ↦ ⟨f, finitePullback s g⟩ vanishes on the finite-dimensional polynomial image.
The previously verified finite Gaussian polynomial density theorem, plus
`Continuous.ext_on`, extends this equality to every g in that finite L² space.
Applying it to finite measurable-set indicators and transporting indicators
through the measure-preserving projection proves that ∫₍cylinder s S₎ f = 0
for every measurable S.

L² membership under this probability measure proves f is integrable. Mathlib's
`generateFrom_measurableCylinders` and `isPiSystem_measurableCylinders` identify
a generating π-system. `MeasurableSpace.induction_on_inter` extends the zero
integral identity from that system to all measurable sets: the whole-space
integral is already zero, complements use `setIntegral_compl`, and disjoint
countable unions use `integral_iUnion` with the proved integrability of f.
`Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero` then gives f = 0 almost
everywhere. The Hilbert orthogonal-complement criterion proves density of the
core. Its proved exact range identity turns this into density of the actual
union of finite-coordinate polynomial spaces. The final approximation theorem
extracts a finite-set, single-polynomial witness from metric density.

Thus finite-dimensional polynomial density is not mistaken for full product
density. Full density follows from an additional proved sigma-algebra argument.
No conditional-expectation convergence, cylinder density, or graph density is
assumed. No L² × L² → L² closure hypothesis is introduced.

### Remaining representation and operator obligations

The density result concerns independent evaluation coordinates ωₙ, which are
already proved to equal W(eₙ) as L² classes. It gives the needed dense scalar
subcore for a future operator. It does not silently restrict the requested
arbitrary-coordinate cylindrical domain to finite-support h vectors.

The following requirements of the larger Malliavin derivative objective remain:

1. Define p(W(h₁), …, W(hₙ)) and its actual ℓ²-valued derivative for arbitrary
   finite families of ℓ² vectors, with proved scalar and vector integrability.
   Infinite-support h vectors need not produce finite-coordinate polynomials
   in the sample evaluations, so this is a genuinely larger core.
2. Prove representation independence across different arbitrary families,
   including correlated and linearly dependent ones. The injectivity proved
   here is for independent coordinate polynomials only. A polynomial vanishing
   on a degenerate Gaussian family's support need not be the zero polynomial.
   One must control its derivative along the actual finite-dimensional Hilbert
   span; formal equality of polynomial expressions is insufficient.
3. Establish substantive product/chain rules, Gaussian integration by parts
   against actual finite-rank polynomial test vector fields, and density of
   the needed vector test space in L²(Ω; ℓ²).
4. Use these identities and dense test spaces to prove closability, with
   operator-domain membership kept separate from the derivative identities.
5. Construct the closed derivative and its densely defined adjoint divergence,
   with explicit actual domains. No graph-norm density, maximal-domain
   characterization, or infinite-dimensional adjoint equality is proved by
   the scalar density theorem established here.

All earlier Gaussian, finite-dimensional operator, spectral-domain, and adjoint
results remain unchanged. Work stops at this scalar density milestone as
requested; the overall Malliavin operator construction remains unfinished.

### Verification of the density milestone

The complete `lake build` succeeds (3347 jobs). Both new modules compile without
warnings; the two existing unused-section-variable warnings in
`Foundation/Adjoint.lean` remain unchanged. A fresh Lean run of the complete
`Foundation/AxiomAudit.lean` produces 513 results for 513 explicit queries,
including all fourteen new declarations. The only dependencies reported are
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or custom
axiom dependency. Raw audit output is retained in the ignored build artifact
`.lake/build/infinite-gaussian-cylinder-density-axioms.log`.

The original Lean/manuscript SHA-256 hashes remain unchanged. All previous proof
modules, the toolchain, and dependency configuration remain unchanged. The root
imports, axiom audit, and documentation are extended for this verified milestone.
The overall Malliavin operator objective remains open beyond scalar core density.

## Recovered milestone: arbitrary isonormal polynomial cylinders and gradients

Baseline: `2d31e09e71daf530c82244a6b7616218f955c83c`.
The interrupted working tree contained only the untracked
`Foundation/InfiniteGaussianCylinders.lean`; all committed files were unchanged.
Its 25 declarations already contained the cylinder construction, integrability
proofs, polynomial gradient and product rules, analytic perturbation argument,
compatibility lemmas, and scalar core density proof. A targeted Lean run found
one unfinished elaboration: the linear-coordinate derivative in
`isonormalCylinderShift_hasFDerivAt` lacked its basepoint. Recovery supplied the
explicit zero Hilbert vector and wrapped the line for the style linter. No
recovered definition, theorem statement, or mathematical hypothesis was changed.
An exact pre-repair copy is preserved in the ignored build artifact
`.lake/build/recovered-infinite-cylinders.lean`.

### Mathematical meaning of the completed declarations

Let H be the already constructed real Hilbert space ℓ², μ the countable product
of standard Gaussian measures, and W : H → L²(μ) the verified isonormal isometry.
For any finite index type I, arbitrary h : I → H, and real polynomial p in I,
write F(h,p)(ω) = p((W(hᵢ)(ω))ᵢ). No orthogonality, independence, nonzero-vector,
finite-support, or rank hypothesis is imposed on h. Actual representatives of
W(hᵢ) are used; their pointwise values are not asserted to satisfy all Hilbert
linear relations simultaneously outside one universal null set.

| Lean declarations | Precise content |
| --- | --- |
| `isonormalCylinder` | The actual scalar polynomial evaluation F(h,p). |
| `isonormalCylinder_C`, `isonormalCylinder_X` | Constants evaluate to constants; a coordinate variable evaluates to W(hᵢ). |
| `isonormalCylinder_add`, `isonormalCylinder_mul` | Evaluation respects polynomial addition and multiplication. |
| `isonormalCylinder_memLp` | F(h,p) belongs to every finite-exponent Lp(μ), proved from the genuine Gaussian marginal laws and doubled-exponent Hölder. |
| `isonormalCylinderGradient` | G(h,p)(ω) = Σᵢ (∂ᵢp)((W(hⱼ)(ω))ⱼ) hᵢ in H; partials are actual polynomial derivatives. |
| `isonormalCylinderGradient_memLp` | G(h,p) belongs to every finite-exponent Lp(μ; H), by scalar polynomial moments and finite sums of fixed Hilbert vectors. |
| `isonormalCylinderL2`, `isonormalCylinderGradientL2` | The scalar and H-valued L² classes obtained from the proved integrability. These are maps of representation data (h,p), not an operator on scalar L² classes. |
| `isonormalCylinderL2_coeFn`, `isonormalCylinderGradientL2_coeFn` | Their Lp representatives agree almost everywhere with F and G, respectively. |
| `isonormalCylinderGradient_C`, `isonormalCylinderGradient_X` | The gradient of a constant is zero; the gradient of the i-th coordinate is hᵢ. |
| `isonormalCylinderGradient_add` | G(h,p+q) = G(h,p) + G(h,q), pointwise. |
| `isonormalCylinderGradient_mul` | G(h,pq) = F(h,p) G(h,q) + F(h,q) G(h,p), proved using the genuine polynomial partial-derivative product rule. |
| `isonormalCylinderShift` | The actual Hilbert-space polynomial Ψ(h,p,ω)(v) = p((W(hᵢ)(ω) + ⟨hᵢ,v⟩)ᵢ). |
| `isonormalCylinderShift_hasFDerivAt`, `isonormalCylinderShift_fderiv` | Ψ has the genuine Fréchet derivative at v=0 given by the continuous linear functional v ↦ ⟨G(h,p)(ω),v⟩. The proof uses analytic constant, sum, and product differentiation. |
| `isonormalCylinderShift_product_rule` | The actual Fréchet derivative at zero of Ψ(h,p,ω) Ψ(h,q,ω) is represented by F(h,p) G(h,q) + F(h,q) G(h,p). |
| `isonormalCylinder_smulGradient_memLp` | Each product-rule term F(h,p) G(h,q) has every finite Lp moment, using both factors at exponent 2r. This is polynomial-core closure, not L² × L² → L² closure. |
| `isonormalCylinderL2_units` | Choosing hᵢ to be the corresponding coordinate unit vectors recovers the existing finite-coordinate polynomial embedding as an L² class. |
| `isonormalCylinderL2_rename_units` | Polynomial renaming along any finite map into ℕ agrees with evaluation at the corresponding isonormal unit vectors; injectivity of that map is not required. |
| `isonormalPolynomialCore` | The set of scalar L² classes represented by some polynomial in an arbitrary finite family of H directions. No derivative graph is attached to this set. |
| `isonormalPolynomialCore_dense` | This scalar set is dense in the entire Gaussian L² space because it contains the previously proved dense coordinate-polynomial subcore. |

The statements allow empty finite index types: the sum defining G is then zero,
and the polynomial is constant. Thus no positive-dimension restriction is hidden.
The new core also allows infinite-support h vectors. Existing independent
coordinate constructions and all prior operator results are preserved.

### Scope of genuine differentiation and the explicit open obligation

The verified derivative is the derivative of the displayed affine-coordinate
function on H for each fixed ω. This is substantive analytic differentiation,
not independently prescribed derivative data. It does not yet identify Ψ with
F evaluated at a translated sample ω+v. Such an identification requires an
almost-everywhere translation argument for the chosen W representatives,
including the relevant Cameron–Martin measure facts; none is assumed here.

Representation independence remains unproved: from
F(h,p) = F(k,q) almost everywhere, one must prove
G(h,p) = G(k,q) almost everywhere, even for different finite index types and
linearly dependent families. The finite-dimensional representation-independence
results do not apply directly to the infinite product sample space. In
particular, a degenerate Gaussian coordinate law does not have full support in
the ambient coordinate space, so scalar equality does not justify formal
polynomial equality or unrestricted equality of coordinate partial derivatives.

A possible noncircular route is to take the common finite-dimensional span of
both families, choose an orthonormal basis, prove its W coordinates have the
standard Gaussian joint law, transport both polynomials using the proved
almost-everywhere linear relations, and apply full-support polynomial
uniqueness and genuine differentiation on that span. The span inclusion must
then transport the gradient identity back to H. These transports and the
common-span comparison are future proof obligations, not hypotheses introduced
into any completed theorem.

Consequently, no Malliavin derivative operator on scalar L² equivalence classes,
infinite-dimensional Gaussian integration by parts, gradient closability,
vector test-space density, divergence adjoint, graph-domain characterization,
or infinite-dimensional adjoint equality is claimed. The present product rules
hold for actual polynomial representations within one chosen family. They do
not discharge the comparison between distinct representations. Full smooth
cylinders and infinite-dimensional chain rules also remain beyond this milestone.

### Verification and preservation

The complete Lake build succeeds (3348 jobs). The recovered module compiles
without warnings after the line wrap; the two pre-existing unused-variable
warnings in `Foundation/Adjoint.lean` remain. The full axiom audit has 538 explicit
queries and 538 verified results, including all 25 recovered declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur: no `sorryAx` or custom
axioms. The raw output is preserved in the ignored build artifact
`.lake/build/infinite-gaussian-cylinders-axioms.log`. A source scan found no
`sorry`, `admit`, or custom axiom declarations in Foundation.

The original Lean and manuscript SHA-256 hashes match the previously recorded
values. Earlier proof modules, toolchain, and dependency lockfile are unchanged.
Only the recovered module, project root import, axiom queries, and documentation
are included in this milestone. This section supersedes the earlier density
milestone's open items about arbitrary-cylinder integrability and polynomial
product differentiation; its representation, integration-by-parts, and operator
obligations remain open as specified above.

## Representation-independent infinite-dimensional polynomial derivative

Baseline: `fb17f970af28169e93e7cc7acab6402123c04e4e`. The starting working tree
was clean. The previous cylinder definitions and all earlier proof modules are
preserved unchanged. This milestone proves the previously explicit
representation-independence obligation and constructs the genuine derivative
on the scalar polynomial cylindrical subspace. It stops before Gaussian
integration by parts or closability.

### Common finite-dimensional Gaussian realization

`Foundation/InfiniteGaussianRepresentation.lean` has seven declarations:

| Declaration | Exact mathematical content |
| --- | --- |
| `finiteGaussianPoint` | For a finite-dimensional real Hilbert space E, an isometric linear inclusion A : E → H, and the standard orthonormal basis (bₐ) of E, defines X_A(ω) = Σₐ W(A bₐ)(ω) bₐ. Here H is the verified ℓ² Hilbert space. |
| `finiteGaussianPoint_measurable` | This actual E-valued random vector is measurable. |
| `finiteGaussianPoint_coordinate` | For every v ∈ E, W(A v) = ⟨v,X_A⟩ almost everywhere, by proved finite-sum W linearity and orthonormal basis reconstruction. |
| `finiteGaussianPoint_law` | μ.map X_A = stdGaussian E, proved by characteristic functions of the preceding coordinates, the verified first-chaos Gaussian law, and ‖A v‖ = ‖v‖. No law or independence is assumed. |
| `isonormalCylinder_finiteGaussianPoint` | F(Ah,p) = cylinder(h,p)(X_A) almost everywhere for every finite family h in E. |
| `isonormalCylinderGradient_finiteGaussianPoint` | G(Ah,p) = A(cylinderGradient(h,p)(X_A)) almost everywhere; the finite and infinite genuine gradient formulas are compatible through the linear inclusion. |
| `isonormalCylinderGradientL2_representation_independent` | For arbitrary finite index types I,J, arbitrary h : I → H and k : J → H, and polynomials p,q, F(h,p) = F(k,q) as scalar L² classes implies G(h,p) = G(k,q) as H-valued L² classes. There are no rank, independence, orthogonality, finite-support, or derivative-equality hypotheses. |

For the last theorem, take S = span(range h ∪ range k) inside H. Finiteness of
both families proves finite dimensionality of S. Equip S with its Borel sigma
algebra, use its standard orthonormal basis, and apply the realization above to
its isometric subtype inclusion A. Each hᵢ and kⱼ is lifted to S using proved
span membership. The scalar transport lemmas and the assumed scalar L² equality
give equality of the two finite-space cylinder functions at X_A almost
everywhere. Their equality set is closed because both functions are continuous,
hence measurable. The proved pushforward law transfers that equality to
stdGaussian S. The previously verified
`FiniteGaussian.cylinderGradient_representation_independent` then gives equality
of their gradients everywhere on S; transport through A and the actual gradient
compatibility lemmas gives equality of the H-valued L² classes.

Full support is used on S, not on the possibly degenerate original coordinate
space. Consequently, dependent-coordinate polynomial evaluation is never
asserted to be injective. The original formal polynomials need not be equal.
The proof also covers S = {0} and empty families: all basis sums and all scalar
projection laws used above remain valid in dimension zero.

### The actual polynomial scalar L² domain and derivative

`Foundation/InfiniteGaussianDerivative.lean` establishes the following:

| Declarations | Mathematical content |
| --- | --- |
| `isonormalCylinderL2_rename` | Renaming polynomial variables along any finite map agrees with composing the Hilbert coordinate family with that map. The scalar statement needs no finite-type hypothesis. |
| `isonormalCylinderGradientL2_rename` | The genuine L² gradients agree under that same renaming, deduced from the proved representation-independence theorem and scalar equality. |
| `isonormalCylinderL2_add`, `isonormalCylinderGradientL2_add` | Polynomial addition gives addition of actual scalar and gradient L² classes. |
| `isonormalCylinderL2_const_mul`, `isonormalCylinderGradientL2_const_mul` | Multiplying a polynomial by a real constant gives scalar multiplication of the actual scalar and gradient classes. |
| `isonormalCylinderL2_mem_core` | A cylinder indexed by any finite type belongs to the original Fin-indexed scalar core, via a proved finite equivalence and renaming. |
| `isonormalPolynomialCore_zero`, `isonormalPolynomialCore_add`, `isonormalPolynomialCore_smul` | Zero, addition, and real scalar multiplication preserve the scalar core. Addition uses a common disjoint-union family, not an assumed closure property. |
| `polynomialCylindricalDomain` | The resulting real submodule of the actual scalar Gaussian L² space, with carrier exactly the previously defined isonormalPolynomialCore. |
| `PolynomialRepresentation`, its four fields, `polynomialRepresentation` | Witness data for a scalar domain element: dimension, Hilbert directions, an actual polynomial, and equality of its evaluated scalar L² class to the element. A witness is chosen noncomputably from proved membership; it contains no independently prescribed derivative value. |
| `polynomialGradient` | The H-valued L² gradient of that chosen representation. |
| `polynomialGradient_agrees` | For every representation (h,p) of f, the chosen value equals G(h,p) in H-valued L², using the proved comparison theorem. Its scalar representation equality is the definition of being a representation, not a gradient-equality assumption. |
| `polynomialGradient_add`, `polynomialGradient_smul` | The representation-independent gradient is a real linear map, with addition compared in a common family and scalar multiplication reduced to constant-polynomial multiplication. |
| `polynomialDerivative` | The genuine linear operator D : polynomialCylindricalDomain → L²(μ; H), implemented as a LinearMap on that submodule. No closed extension is asserted. |
| `polynomialCylindricalDomain_dense` | Its scalar domain is dense in the full ambient Gaussian L² space, using the already proved core-density theorem. |
| `polynomialDerivative_on_cylinder` | D of the domain element represented by F(h,p) equals G(h,p), for every finite representation. |
| `polynomialDerivative_empty` | For any polynomial in an empty coordinate family, the actual domain derivative is zero. |

Noncomputable witness choice affects neither operator values nor the operator's
mathematical meaning: `polynomialGradient_agrees` proves that every witness has
the same value. No arbitrary representation-independence hypothesis or custom
axiom is introduced. The derivative is a densely defined linear operator on the
polynomial domain; no domain of a closure is being substituted for this domain.

### Intrinsic products and Leibniz with correct integrability

`Foundation/InfiniteGaussianPolynomialProducts.lean` has thirteen declarations:

| Declarations | Mathematical content |
| --- | --- |
| `exists_common_polynomial_representation` | Any two scalar domain elements admit a common finite Hilbert family and two actual polynomials representing them. The construction combines their witnesses and renames into one Fin-indexed family. |
| `polynomialDomain_memLp`, `polynomialDerivative_memLp` | Actual representatives of every domain element and its genuine derivative have every finite Lp moment, by almost-everywhere transport of the earlier polynomial moment proofs. |
| `polynomialDomain_mul_memLp` | The product of two domain elements' scalar representatives has every finite Lp moment; exponent r uses both input moments at 2r and Hölder. |
| `polynomialProductL2`, `polynomialProductL2_coeFn` | The actual scalar L² class of their pointwise product and its almost-everywhere representative identity. |
| `polynomialProductL2_agrees` | In any common polynomial representation, this actual L² product equals the evaluation class of p q. |
| `polynomialProductL2_mem_domain` | This product belongs to the scalar cylindrical subspace, proved from a common representation and polynomial multiplication. |
| `polynomialProduct` | Multiplication of actual domain elements, returning a domain element with the proved membership witness. |
| `polynomialDomain_smul_derivative_memLp` | f Dg has every finite Lp moment; in particular, L⁴ × L⁴ → L² proves membership at r=2. |
| `polynomialTimesDerivative`, `polynomialTimesDerivative_coeFn` | The actual H-valued L² class of f Dg and its almost-everywhere representative identity. |
| `polynomialDerivative_product` | For all actual domain elements f,g, D(polynomialProduct f g) = polynomialTimesDerivative f g + polynomialTimesDerivative g f as H-valued L² classes. This is the intrinsic Leibniz identity D(fg)=f Dg+g Df. |

Product closure and the Leibniz identity have separate proofs. Membership is
established through scalar polynomial multiplication and higher moments before
the derivative identity is proved. The identity then uses genuine partial
differentiation in a common representation and the independently established
representation comparison. This does not introduce L² × L² → L² closure outside
the polynomial domain, nor boundedness of polynomial multiplication on L².

### Verification, dependencies, and remaining obligations

The full `lake build` passes (3351 jobs). All three new modules compile without
warnings; only the two pre-existing unused-variable warnings in Adjoint remain.
The complete axiom audit includes 583 queries and 583 results: all earlier 538
queries plus 45 queries for the new declarations and representation fields.
The dependency union is only `propext`, `Classical.choice`, and `Quot.sound`;
there is no `sorryAx` or custom axiom. The raw audit output is saved as the ignored
build artifact `.lake/build/infinite-gaussian-representation-axioms.log`.

Earlier proof modules, the original Lean source and manuscript, toolchain, and
dependency configuration remain unchanged. Root imports, axiom queries, and
project documentation are extended for these three new modules.

Representation independence is now proved for polynomial cylinders on the
verified countable-product isonormal model over H = ℓ². This supersedes the open
representation obligation of the preceding milestone. Extension to a general
abstract separable Hilbert space/model, non-polynomial smooth cylinder classes,
and translation compatibility of sample representatives are not claimed here.
Gaussian integration by parts for this actual infinite-dimensional operator,
density of the necessary vector test fields, closability, its closed extension,
divergence adjoints, and graph-domain characterizations remain unproved. No
closed-domain algebra or graph-norm density assertion is inferred from the
polynomial-domain product rule. The next analytic milestone is Gaussian
integration by parts with proved test-space density, then closability.

## Genuine Gaussian IBP, dense finite-rank divergence fields, and closability

Baseline: `baa5f859a066e6eb5b57ad3f16c2bcd25221cb36`. The starting working tree
was clean. This milestone preserves the existing polynomial derivative,
representation independence, scalar domain, and product results. It establishes
Gaussian integration by parts and closes the actual polynomial derivative on
the verified countable-product isonormal model over H = ℓ².

### Directional finite-Hilbert Gaussian analysis

`Foundation/FiniteGaussianDirectionalIBP.lean` has five declarations:

| Declaration | Exact mathematical meaning |
| --- | --- |
| `basisPolynomialMap` | For arbitrary finite hᵢ in a finite-dimensional Hilbert space E, substitutes the genuine linear polynomial Σₐ ⟨hᵢ,bₐ⟩ Xₐ into p, where (bₐ) is the standard orthonormal basis of E. This is a ring homomorphism of actual polynomial algebras. |
| `basisPolynomialMap_eval` | Evaluation of that substituted polynomial at y is exactly p((⟨hᵢ,Σₐ yₐ bₐ⟩)ᵢ). No coordinate-rank assumption is imposed. |
| `basisPolynomialMap_pderiv_eval` | Its a-th evaluated partial derivative is ⟨cylinderGradient(h,p)(Σₐ yₐ bₐ),bₐ⟩. The proof differentiates the actual substituted polynomial, using the true polynomial product rule. |
| `cylinder_stein_basis` | E[⟨gradient(h,p),bₐ⟩] = E[cylinder(h,p) ⟨bₐ,x⟩] under stdGaussian E, transported from the previously proved independent-coordinate polynomial Stein theorem. |
| `cylinder_stein` | E[⟨gradient(h,p),v⟩] = E[cylinder(h,p) ⟨v,x⟩] for every v ∈ E, by orthonormal reconstruction, proved integrability, and finite-sum integration. |

This is the missing analytic bridge between the original independent-coordinate
IBP theorem and arbitrary finite Hilbert families. It does not treat correlated
coordinates as independent tensor coordinates. Empty index families and
zero-dimensional Hilbert spaces are allowed.

### Actual vector test core and its proved density

`Foundation/InfiniteGaussianVectorCore.lean` has eight declarations:

| Declarations | Exact mathematical meaning |
| --- | --- |
| `GaussianVectorL2` | Mathlib L²(μ; H), using the genuine ℓ² Hilbert fiber norm. |
| `scalarTensor`, `scalarTensor_coeFn` | The bounded linear map f ↦ f h from scalar L² to H-valued L², and its actual almost-everywhere representative formula. It uses the existing continuous-linear-map Lp composition infrastructure. |
| `cylindricalVectorDomain` | The algebraic span of actual G h fields, with G in the already verified scalar polynomial cylindrical subspace and h arbitrary in H. |
| `scalarTensor_mem_domain` | Every such rank-one polynomial field belongs to that core. |
| `scalarTensor_inner` | ⟨f h,u⟩ in vector L² equals the scalar L² pairing of f with the actual projected field ⟨h,u⟩. |
| `eq_zero_of_cylindricalVector_orthogonal` | A vector L² field orthogonal to every rank-one polynomial field is zero. Scalar cylinder density first kills every scalar projected field; countably many ℓ² unit-coordinate projections then kill its actual representative almost everywhere. |
| `cylindricalVectorDomain_dense` | This core is dense in the entire H-valued Gaussian L² space, by the Hilbert orthogonal-complement criterion. |

Density is not assumed from scalar density alone. The proof establishes the
projection pairing, uses the already proved scalar density, and separately
uses completeness of the ℓ² coordinate system. The later exact finite-sum
characterization and norm-approximation theorem identify the dense set with
genuine finite-rank polynomial fields, rather than an unspecified vector domain.

### Genuine infinite-cylinder Stein and rank-one IBP

`Foundation/InfiniteGaussianIBP.lean` has nine declarations:

| Declarations | Exact mathematical meaning |
| --- | --- |
| `isonormalCylinder_stein` | For arbitrary finite h, polynomial p, and v ∈ H, E[⟨G(h,p),v⟩] = E[F(h,p) W(v)]. The proof transports both sides to the standard Gaussian on span(range h ∪ {v}) using the previously proved genuine finite realization and gradient compatibility. |
| `polynomialDerivative_stein` | The same identity E[⟨D₀F,v⟩] = E[F W(v)] on the actual representation-independent scalar L² polynomial domain. |
| `polynomial_times_firstChaos_memLp` | F W(h) has every finite Lp moment. At exponent r, both input moments at 2r are proved and Hölder is applied. |
| `polynomial_directional_memLp` | ⟨D₀G,h⟩ has every finite Lp moment, using the proved vector derivative moments and a fixed Hilbert direction. |
| `rankDivergence_memLp` | G W(h) − ⟨D₀G,h⟩ has every finite Lp moment. |
| `rankDivergence`, `rankDivergence_coeFn` | Its actual scalar L² class and the proved almost-everywhere expression δ₀(Gh)=G W(h)−⟨D₀G,h⟩. |
| `polynomialDerivative_rank_integration_by_parts` | E[⟨D₀F,Gh⟩] = E[F rankDivergence(G,h)] for all scalar polynomial-domain F,G and arbitrary h ∈ H. This follows from Stein applied to the proved intrinsic polynomial product and the actual product derivative. |
| `polynomialDerivative_rank_pairing` | The corresponding Hilbert-space pairing identity ⟨D₀F,Gh⟩_{L²(H)} = ⟨F,rankDivergence(G,h)⟩_{L²}. |

The rank-one IBP proof establishes integrability before splitting sums or
subtracting integrals: F⟨D₀G,h⟩ and G⟨D₀F,h⟩ use L² × L² → L¹; F(GW(h)) uses
the independently proved L² membership of GW(h). Fourth moments justify that
membership. No L² × L² → L² closure is assumed.

### Single-valued cylindrical divergence, closed derivative, and full adjoint

`Foundation/InfiniteGaussianOperators.lean` has forty-one declarations. They
establish the following definitions and exact statements:

| Declarations | Exact mathematical meaning |
| --- | --- |
| `cylindricalDerivative` | D₀ as a Mathlib LinearPMap on ambient scalar L², with domain exactly polynomialCylindricalDomain and value exactly polynomialDerivative. |
| `cylindricalDivergenceGraph` | The algebraic span of the pairs (G h, G W(h)−⟨D₀G,h⟩) of actual L² classes. No independently prescribed output is introduced. |
| `cylindricalDivergenceGraph_pairing` | Every pair (u,v) in that span satisfies ⟨D₀F,u⟩=⟨F,v⟩ for every scalar polynomial test F. Proved rank-one IBP puts the generators in the kernel of the actual pairing-difference linear functional, hence also their span. |
| `cylindricalDivergenceGraph_vertical_zero` | If (0,v) belongs to this graph, then v=0. The pairing identity and proved scalar density force v to vanish. This proves divergence single-valuedness, rather than assuming it. |
| `cylindricalDivergence`, `cylindricalDivergence_graph` | The genuine partial linear operator δ₀ obtained from this proved single-valued graph, with its graph equal to the explicitly generated graph. |
| `cylindricalDivergence_rank_graph` | Each actual rank-one field has precisely its explicit rankDivergence value in δ₀'s graph. |
| `cylindricalDivergence_domain` | The domain of δ₀ is exactly cylindricalVectorDomain; both inclusions are proved. |
| `cylindricalDerivative_dense_domain`, `cylindricalDivergence_dense_domain` | Both actual operator domains are dense in their respective ambient L² spaces. |
| `cylindricalDerivative_formalAdjoint` | The Hilbert IBP identity on both actual restricted operator domains. |
| `cylindricalDerivative_le_divergence_adjoint`, `cylindricalDivergence_le_derivative_adjoint` | D₀ ⊆ δ₀* and δ₀ ⊆ D₀*, with domain inclusion and values proved from IBP and the relevant proved domain density. |
| `cylindricalDerivative_isClosable` | D₀ is closable because it is contained in the closed adjoint δ₀* of a densely defined operator. This uses the genuine IBP and vector density already proved. |
| `cylindricalDivergence_isClosable` | δ₀ is also closable, using its proved inclusion in the closed adjoint D₀*. |
| `closedCylindricalDerivative`, `closedCylindricalDerivative_isClosed`, `closedCylindricalDerivative_dense_domain` | D is the actual graph closure of D₀; closability proves that it is a closed densely defined operator. |
| `closedCylindricalDerivative_graph`, `closedCylindricalDerivative_mem_iff` | graph(D)=closure(graph(D₀)); F∈Dom(D) iff there exists V∈L²(μ;H) with (F,V) in that graph closure. These are exact graph domains, with no unproved Sobolev characterization imposed. |
| `hilbertDivergence` | The full natural Hilbert-space adjoint δ=D*. |
| `hilbertDivergence_eq_cylindricalDerivative_adjoint` | D*=D₀*, by the previously proved generic closure-adjoint theorem and the newly proved closability and density. |
| `cylindricalDivergence_le_hilbertDivergence` | δ₀ ⊆ δ, with actual domain and value inclusion. |
| `hilbertDivergence_isClosed`, `hilbertDivergence_dense_domain` | δ is closed because D is densely defined, and is densely defined because its domain contains the proved dense domain of δ₀. |
| `hilbertDivergence_mem_iff` | u∈Dom(δ) iff there exists v∈scalar L² such that ⟨DF,u⟩=⟨F,v⟩ for every F∈Dom(D). This is an exact weak-divergence domain characterization proved from the natural adjoint definition and its pairing identity. |
| `cylindricalField`, `cylindricalDivergenceExpression` | The actual finite sums u=Σⱼ Gⱼ hⱼ and v=Σⱼ(GⱼW(hⱼ)−⟨D₀Gⱼ,hⱼ⟩), for arbitrary finite index types. |
| `cylindricalDivergence_field_graph`, `cylindricalField_mem_domain`, `cylindricalDivergence_field_apply` | Every finite sum belongs to δ₀'s domain, its explicit sum expression is in the graph, and applying δ₀ gives that expression for any domain proof. |
| `cylindricalDivergence_representation_independent` | If two arbitrary finite decompositions give the same H-valued L² field, their divergence sum expressions are equal as scalar L² classes. This follows from the proved graph single-valuedness; no decomposition-independence hypothesis is used. |
| `cylindricalField_integration_by_parts` | For every scalar polynomial F and every actual finite-rank cylindrical u, E[⟨D₀F,u⟩]=E[F δ₀u]. |
| `cylindricalField_ibp_integrable` | Both integrands in that finite-field identity are integrable, proved by vector Hölder and scalar L² product integrability. |
| `closedCylindricalDerivative_core_graph`, `closedCylindricalDerivative_core_mem`, `closedCylindricalDerivative_core_apply` | Every original scalar polynomial-domain F belongs to Dom(D), and DF retains exactly its genuine polynomial derivative D₀F. |
| `hilbertDivergence_field_graph` | The full adjoint δ contains every finite-rank field with precisely the explicit cylindrical divergence value. |
| `cylindricalVectorDomain_mem_iff` | The vector core consists exactly of finite sums Gⱼ hⱼ, with a Fin n representation. The proof extracts finite span witnesses and absorbs real coefficients into the scalar polynomial-domain elements. |
| `closedCylindricalDerivative_le_cylindricalDivergence_adjoint` | D ⊆ δ₀* is a proved closed-operator inclusion. No equality is inferred. |
| `exists_cylindricalField_approx` | For every u∈L²(μ;H) and ε>0, there is one genuine finite-rank polynomial field Σⱼ Gⱼhⱼ with L² distance less than ε. |

Thus operator-domain membership, actual expressions, integration by parts,
single-valuedness, and closability are separate verified steps. The natural
adjoint domain uses the ambient L² norm on Dom(D), not an assumed graph-norm
boundedness condition. Its weak divergence v is uniquely determined because
Dom(D) is dense. No arbitrary adjoint-domain or graph-density assumption occurs.

### Exact remaining obligations and verification

The strongest proved relations here are
D₀ ⊆ δ₀*, D=closure(D₀) ⊆ δ₀*, and δ₀ ⊆ D₀*=D*=δ.
These do not establish closure(δ₀)=δ or D=δ₀*. A graph-core/essential-adjointness
argument would be needed for those stronger identifications. No graph-norm
density of the vector polynomial core in Dom(δ) has been proved here.

All construction remains on the genuine countable-product Gaussian model over
H=ℓ², allowing arbitrary directions, including infinite-support, dependent,
correlated, and zero directions. Extension to other abstract Hilbert models,
non-polynomial smooth cylinders, sample-space translation/Cameron–Martin
compatibility, maximal Sobolev or chaos spectral domains, and advanced stochastic
calculus/Itô results remain future work. No multiplication-algebra claim is made
for Dom(D) or Dom(δ), and no equality with a bounded energy-space interface is
assumed.

The full Lake build passes (3355 jobs). All four new modules compile without
warnings; the two existing unused-variable warnings in Adjoint remain unchanged.
The complete axiom audit has 646 queries and 646 results, including all 63 new
declarations. Its dependency union is only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorryAx` or custom axioms occur. The raw output is retained in
`.lake/build/infinite-gaussian-ibp-closability-axioms.log`, an ignored build
artifact. The Foundation source scan finds no `sorry`, `admit`, or custom axiom
declarations.

The original Lean and manuscript hashes and all earlier proof modules remain
unchanged. Only these four new proof modules, root imports, axiom queries, and
documentation are included. This section supersedes the preceding milestone's
open IBP, vector density, closability, and natural closed-operator/adjoint
construction obligations, while preserving the explicit unresolved graph-core
and full-domain identification obligations above.

## Finite-coordinate divergence graph approximation (continuing 65a6afbf)

### Outcome and scope

This milestone proves that every maximal divergence graph on a finite set of
independent Gaussian coordinates embeds in the graph closure of the genuine
infinite-dimensional polynomial divergence. Its total-degree Hermite
approximations converge in the actual infinite-space divergence graph norm,
preserving cancellations. It also proves the operator-first identity δ* = D
for the full divergence δ = D*, and proves that the two requested polynomial
core identities are equivalent. Neither polynomial core identity is asserted.

The model is still Ω = ℝ^ℕ with countable product standard Gaussian measure μ,
H = ℓ²(ℕ;ℝ), scalar L²(μ), and vector L²(μ;H). Existing arbitrary-direction
polynomial cylinders, including dependent, correlated, and infinite-support
directions, are preserved. The new tensor truncations apply specifically to
finite sets of independent standard coordinates, not to arbitrary correlated
coordinate lists.

### Exact new definitions and statements

`Foundation/AdjointBidual.lean` supplies two reusable real Hilbert-space theorems:

- `closedOperator_adjoint_adjoint_eq`: if T is closed and both T and T* have
  dense ambient domains, T** = T. The reverse inclusion uses orthogonal
  separation of the closed graph in the Hilbert product `WithLp 2 (E × F)`.
- `closableOperator_adjoint_adjoint_eq_closure`: if T is closable and both
  ambient domains are dense, T** = closure(T). The proof uses the preceding
  theorem and the already verified fact that graph closure leaves T* unchanged.

No graph-density assumption occurs in either statement. All their density
hypotheses are discharged by existing concrete theorems in the applications.

`Foundation/InfiniteGaussianFiniteSectors.lean` defines and proves:

| Declaration | Exact mathematical meaning |
| --- | --- |
| `coordinatePolynomialDomain s p` | The actual class p((ωᵢ)ᵢ∈s), as a member of the existing intrinsic scalar polynomial domain. Membership follows from unit-direction isonormal cylinders. |
| `coordinatePolynomialDomain_derivative_coeFn` | Its actual derivative is almost everywhere Σᵢ∈s (∂ᵢp)((ωⱼ)ⱼ∈s)eᵢ. The proof uses the representation-independent genuine derivative, not prescribed derivative values. |
| `finiteVectorPullback s` | A bounded linear map Jₛ from finite vector Gaussian L² to L²(μ;H), defined by Jₛu = Σᵢ∈s eᵢ Iₛ(uᵢ), where Iₛ is the previously verified scalar isometric pullback and uᵢ is the actual L² component. |
| `finiteVectorPullback_apply`, `finiteVectorPullback_polynomial` | The exact component sum formula and its identification with an actual finite-rank cylindrical field for polynomial vectors. |
| `rankDivergence_coordinate` | δ₀(p eᵢ) is the actual pullback of xᵢp − ∂ᵢp. The derivative contribution is computed using actual partial derivatives and orthogonality of the coordinate units. |
| `finitePolynomialDivergence_lift_graph` | For every finite polynomial vector u, (Jₛu, Iₛδ₀,ₛu) belongs to the existing genuine infinite δ₀ graph. |
| `closedPolynomialDivergence` | Exactly closure(δ₀), using the already proved closability; it is not defined to be δ. |
| `closedPolynomialDivergence_isClosed` | This actual graph closure is closed. |
| `closedPolynomialDivergence_le_hilbertDivergence` | closure(δ₀) ⊆ δ, including domains and values, by closed-extension minimality. |
| `closedPolynomialDivergence_adjoint_eq` | closure(δ₀)* = δ₀*. |
| `finiteDivergence_truncation_lift_graph` | If (u,g) lies in the full finite adjoint ∇₀,ₛ* graph, then (Jₛu≤N, Iₛg≤N+1) lies in the genuine infinite polynomial δ₀ graph for every N. |
| `finiteDivergence_truncation_lift_tendsto` | Both coordinates of these lifted truncations converge in their infinite-space L² norms to (Jₛu,Iₛg). |
| `finiteDivergence_truncation_lift_graphNorm_tendsto` | The squared graph error ‖Jₛu≤N − Jₛu‖² + ‖Iₛg≤N+1 − Iₛg‖² tends to zero. This convergence lemma is separate from graph membership. |
| `finiteDivergence_lift_closed_graph` | Every full maximal finite divergence pair (u,g) lifts to graph(closure(δ₀)). This follows from the explicit polynomial graph sequence. |
| `finiteDivergence_lift_hilbert_graph` | The same pair belongs to graph(δ), with the same value. |
| `finiteDivergence_coefficients_lift_closed_graph` | If the actual scalar coefficients of g equal the combined divergence coefficients of u, the lifted pair belongs to graph(closure(δ₀)). This uses proved finite coefficient realization; equality of coefficients is the exact spectral graph condition, not a presumed core property. |
| `finiteDivergence_domain_lift` | The genuine condition Σβ bβ² < ∞ supplies an actual scalar g and puts (Jₛu,Iₛg) in graph(closure(δ₀)). Integrability and realization are proved by the existing finite spectral theorem. |
| `finiteVectorPullback_empty` | J∅u = 0; all finite-sector graph theorems also allow dimension zero. The finite adjoint restricts its scalar output to zero in that dimension. |
| `coordinatePolynomialDomain_derivative_lift` | D₀(Iₛp) = Jₛ(∇₀,ₛp), as actual vector L² classes. |
| `finitePolynomialGradient_lift_graph` | Every finite polynomial gradient graph lifts to the genuine infinite D₀ graph. |
| `finiteGradient_lift_closed_graph` | Every full maximal finite gradient graph lifts to graph(D), by the proved finite Hermite graph approximations. |
| `hilbertDivergence_adjoint_eq_closedDerivative` | δ* = D, using D's proved closedness, D-domain density, and δ-domain density. |
| `cylindricalDivergence_adjoint_dense_domain` | Dom(δ₀*) is dense because it contains the already proved dense Dom(D). |
| `cylindricalDivergence_adjoint_adjoint_eq_closedPolynomialDivergence` | δ₀** = closure(δ₀), using concrete closability and both concrete density proofs. |
| `polynomialDivergence_core_iff_adjoint_identification` | closure(δ₀) = δ if and only if δ₀* = D. Taking adjoints uses the proved identities above. This equivalence does not establish either equality. |

### Combined coefficients and cancellation

For u in a finite coordinate sector the spectral divergence condition is

    bβ = Σᵢ:βᵢ≥1 √βᵢ uᵢ,β−eᵢ,
    Σβ |bβ|² < ∞.

Every vector component uses the same total-degree cutoff |α| ≤ N. A coefficient
contributing to bβ has degree |β|−1, regardless of which component contributes.
Thus the finite theorem `divergenceCoefficient_truncation` retains the entire
sum when |β| ≤ N+1 and removes it otherwise. The lifted graph theorem reuses
that exact result. It never demands Σᵢ,α (αᵢ+1)|uᵢ,α|² < ∞, which would be
stronger and would exclude legitimate cancellations. Scalar coefficient
realization and graph membership are established before the graph limit is used.

### Exact remaining analytic bridge

L² density of polynomial fields does not imply graph density in Dom(δ).
The unproved step is approximation of an arbitrary full infinite divergence
pair by maximal finite-coordinate divergence pairs. This milestone handles
all inner Hermite approximations after such a finite pair has been obtained.

A concrete sufficient bridge is the following finite-coordinate conditional
expectation theorem, which is NOT assumed or formalized as an axiom:

Let Sₙ = {0,...,n−1}, let Eₙ be conditional expectation onto σ(ωᵢ : i∈Sₙ),
and let πₙ be the Hilbert projection onto span{eᵢ : i∈Sₙ}. For every F∈Dom(D),

    EₙF ∈ Dom(D),    D(EₙF) = πₙ Eₙ(DF).

Here vector conditional expectation acts on the H-valued random field before
πₙ. The required next construction identifies scalar finite pullbacks with
that measurable subspace and identifies Jₛ with its finite vector counterpart.
Mathlib already provides `condExpL2`, its contraction property, and its
almost-everywhere agreement with conditional expectation in
`MeasureTheory/Function/ConditionalExpectation/CondexpL2.lean` and `Basic.lean`.
The missing result is compatibility with this project's genuine cylindrical
D and the finite Gaussian operators, not existence of conditional expectation.

For arbitrary-direction polynomial cylinders, a noncircular route is to split
each h into πₙh and (1−πₙ)h, prove Gaussian independence of these orthogonal
families, integrate the residual polynomial using its established Gaussian
moments, and prove the displayed derivative identity by actual polynomial
partial differentiation. Contraction and closedness then extend it to Dom(D).
This remains an obligation, including infinite-support h; it is not supplied
as a hypothesis to any completed theorem.

Duality would then give, for every (u,v)∈graph(δ),

    uₙ = πₙ Eₙu ∈ Dom(δ),    δuₙ = Eₙv,

and identify (uₙ,Eₙv) with an actual finite adjoint graph. One must additionally
prove uₙ→u in vector L² and Eₙv→v in scalar L². The existing scalar polynomial
density and coordinate completeness can supply this convergence with the
uniform contraction estimates; an L¹ martingale limit alone is insufficient.
Combining these outer approximations with the now verified inner Hermite
approximations would prove closure(δ₀)=δ, and then δ₀*=D by the verified
bidual equivalence. No mathematical counterexample to either equality is
claimed; the obstruction here is an unfinished analytic compatibility proof.

### Operator-first manuscript identification

`OperatorDerivative.lean:57–80` defines the operator derivative as the natural
unbounded adjoint. `OperatorDerivative.tex:48–52` takes δ as primitive and
`OperatorDerivative.tex:500–504` describes the Gaussian cylindrical derivative,
its graph closure, and the Skorokhod adjoint. The verified concrete full δ now
recovers exactly D = δ*. This is a valid operator-first identification on the
countable Gaussian model, without presuming the polynomial divergence core.
Choosing δ₀ or closure(δ₀) as the primitive integral would instead give δ₀*,
which is only known to contain D. Its equality with D is precisely the open
core problem. None of these statements supplies predictable isometry, PRP,
Clark–Ocone hypotheses, or an identification with the original bounded energy
interface. The polynomial core is distinct from the manuscript's smooth
bounded cylindrical core; equality of their graph closures is not asserted.

### Verification

The complete `lake build` passes (3357 jobs). Both new proof modules compile
without warnings; the two longstanding unused-variable warnings in Adjoint
are unchanged. The complete axiom audit has 674 queries and 674 results,
including all 28 new declarations. Its dependency union is only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or custom axiom.
The raw output is retained in the ignored artifact
`.lake/build/infinite-gaussian-finite-sectors-axioms.log`. The Foundation
source scan finds no `sorry`, `admit`, or custom axiom declarations.
The original Lean and TeX sources and all earlier proof modules are unchanged.

## Finite-coordinate weak-gradient bridge (current milestone)

The two target identities remain **unproved**:

    closure(δ₀) = δ = D*,       δ₀* = D.

The existing finite-sector Hermite truncation gives graph approximation **after**
an infinite field has been identified with a maximal finite-sector divergence
pair. It does not provide finite-sector graph approximation of arbitrary
`u ∈ Dom(δ)`. The bidual theorem proves the displayed identities equivalent,
but neither follows from L² density alone.

`Foundation/InfiniteGaussianCoordinateFields.lean` now establishes the following
additional facts with the actual product Gaussian measure and operators:

| Declaration | Mathematical statement |
| --- | --- |
| `coordinatePolynomialVectorDomain` | The algebraic span of fields `p(ω|ₛ)eₙ`, where `s` is finite and `p` is a genuine polynomial on that finite coordinate space. |
| `coordinatePolynomialVectorDomain_le` | Every such field belongs to the actual polynomial divergence domain. This follows from the existing rank-field graph, without asserting graph closure. |
| `coordinatePolynomialVectorDomain_dense`, `exists_coordinatePolynomialVector_approx` | These finite-coordinate fields approximate every `L²(Ω;ℓ²)` field in the **ambient L² norm**. The proof uses verified scalar polynomial density and the completeness of the coordinate vectors in `ℓ²`. |
| `finiteVectorPullback_insert`, `coordinatePolynomialVector_mem_finite_sector` | A rank-one coordinate field is the pullback of a genuine finite Gaussian vector field after enlarging its coordinate set to include its output direction. |
| `eq_zero_of_finiteVectorPullback_orthogonal` | The ranges of all finite vector lifts jointly detect every vector `L²` class. This is an orthogonality statement; it is not convergence of the associated adjoint projections. |
| `finiteSector_weak_gradient_graph` | If `(F,G) ∈ graph(δ₀*)`, then `(Iₛ*F,Jₛ*G) ∈ graph(δ₀,ₛ*)` for every finite `s`, where `Iₛ` and `Jₛ` are the established scalar and vector lifts. The proof uses the actual polynomial divergence lift and Hilbert adjoint pairings. |
| `finiteSector_weak_gradient_lift_graph` | Every projected pair `(IₛIₛ*F,JₛJₛ*G)` lies in `graph(D)` by the previously verified finite-dimensional Hermite graph theorem. No convergence is asserted. |
| `finiteScalarProjection_fix`, `finiteScalarProjection_norm_le`, `exists_finiteScalarProjection_approx` | `IₛIₛ*` fixes the finite scalar sector, is contractive, and its finite-sector choices approximate every scalar Gaussian `L²` class in norm. This uses proved polynomial density and the Hilbert adjoint of the isometric pullback. |

These statements apply to all finite `s`, including the empty set. They do not
replace the maximal finite vector divergence condition by componentwise
Sobolev bounds; the previous finite graph theorem still uses the combined
Hermite coefficients and permits cancellation.

The exact missing step is **joint finite-sector projection convergence** on
the graph of `δ₀*` (equivalently, an appropriate conditional-expectation
commutation theorem): find finite sets `sₙ` such that both

    Iₛₙ Iₛₙ* F → F          in scalar L²,
    Jₛₙ Jₛₙ* G → G          in vector L²

for each `(F,G) ∈ graph(δ₀*)`. The scalar approximation above is existential
and does not by itself give a common sequence with the vector approximation.
The vector lift has not yet been proved isometric or its adjoint compositions
identified with finite-coordinate conditional expectation and direction
projection. The joint density of its ranges, proved here, is strictly weaker
than convergence of `JₛJₛ*`. With this additional noncircular projection result,
closedness of `D` and `finiteSector_weak_gradient_lift_graph` would yield
`δ₀* ≤ D`; the reverse inclusion and existing bidual theorem would then give
both desired identities. No theorem in this milestone assumes that convergence.

Mathlib already supplies bounded Hilbert adjoints, `condExpL2`, Gaussian
product measures, and the `L²` infrastructure. Public `gaussian-hilbert`
contains finite Hermite completeness, while `lean-malliavin` has a closed
Gaussian Banach-space Malliavin derivative and simple-field divergence. Their
interfaces do not directly supply this project's finite-lift projection
compatibility, so no new dependency was introduced. The inspected sources are
`https://github.com/mrdouglasny/gaussian-hilbert/blob/4d055b0bf3722c73bd6c327eeabd8a8a72ab4c7e/GaussianHilbert/HermitePolynomials.lean`
and `https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/MalliavinDerivative.lean`.

The complete `lake build` passes (3358 jobs), and the separately built
`Foundation.AxiomAudit` has 688 queries and 688 results. Every new declaration
depends only on some subset of `propext`, `Classical.choice`, and `Quot.sound`;
none depends on `sorryAx` or a custom axiom. The source scan found no
`axiom`, `sorry`, or `admit` declaration. The audit transcript is kept in the
ignored file `.lake/build/infinite-gaussian-coordinate-fields-axioms.log`.

### Complete divergence graph core on the countable Gaussian product

`Foundation/InfiniteGaussianProjectionConvergence.lean` resolves the projection
obligation left above. The theorem applies to the established countable product
of independent standard real Gaussians, with ambient fiber `ℓ²(ℕ)` and genuine
polynomial-cylinder operators. It does not introduce a componentwise
Sobolev-domain condition or assume graph density.

The finite fiber map sends `x ∈ ℝˢ` to `Σᵢ∈s xᵢ eᵢ ∈ ℓ²(ℕ)`.
`finiteFiberMap_orthonormal` and `finiteFiberIsometry` verify that this is an
isometry, including for `s = ∅`. Its pointwise `L²` lift and the
measure-preserving finite Gaussian projection give `finiteVectorIsometry`.
`finiteVectorPullback_eq_isometry` proves that this is **the previously defined
vector lift** `Jₛ`, so `JₛJₛ*` is a contractive orthogonal projection, not a
new, independently prescribed approximation.

`finiteVectorProjection_fix_coordinate_of_subset` proves that a field
`p(ω|ₛ)eₙ` is fixed whenever the finite sector contains `s ∪ {n}`. Span
induction gives `finiteVectorProjection_eventually_fix_core`; the verified
ambient density of these polynomial fields and uniform projection contraction
give `finiteVectorProjection_range_tendsto`:

    J_[0,N) J_[0,N)* G → G  in L²(Ω;ℓ²), for every G.

The parallel result `finiteScalarProjection_range_tendsto` gives
`I_[0,N) I_[0,N)* F → F` for every scalar `L²` class. Thus
`finiteSector_projections_range_tendsto` is a **simultaneous** limit along the
same increasing sets. For a pair `(F,G) ∈ graph(δ₀*)`, the previously proved
finite-dimensional Hermite weak-gradient bridge places every projected pair
in `graph(D)` (`finiteSector_weak_gradient_range_graph`). Closedness of `D`
then proves `cylindricalDivergence_adjoint_le_closedDerivative`. Combining the
earlier reverse inclusion and bidual equivalence yields the exact identities

    δ₀* = D,
    closure(δ₀) = δ = D*.

The Lean declarations are `cylindricalDivergence_adjoint_eq_closedDerivative`
and `closedPolynomialDivergence_eq_hilbertDivergence`. The latter is a genuine
graph-core assertion: `hilbertDivergence_polynomial_graph_core_sequence`
constructs, for each `(u,g) ∈ graph(δ)`, a sequence in the actual polynomial
divergence domain whose field and divergence converge jointly to `(u,g)`.
The finite-dimensional spectral theorem used in the weak-gradient lift retains
the **combined** divergence coefficients `b_β`; it does not require
componentwise weighted summability. The proof does not infer graph convergence
from ambient `L²` density alone: isometric projection convergence and closedness
are the additional steps.

No unresolved analytic obligation remains for the polynomial divergence graph
core on this countable standard Gaussian product. Extensions to a general
Gaussian probability space or an arbitrary nonseparable isonormal index space
require separate transfer/density arguments. This milestone does not assert an
Itô formula or stochastic integration theory.

Verification for this milestone: the full `lake build` and
`lake build Foundation.AxiomAudit` pass. The audit contains 714 `#print axioms`
queries with 714 results. Each new declaration depends only on a subset of
`propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx` or a custom
axiom. The source scan finds no `axiom`, `sorry`, or `admit` declaration. The
audit transcript is in the ignored file
`.lake/build/infinite-gaussian-projection-axioms.log`.

## Gaussian entropy M1: finite square entropy from L4 (2026-10-11)

Implemented `Foundation/GaussianEntropy.lean`, following M1 of
`BAKRY_EMERY_REPLACEMENT_PLAN.md`. The module defines, for real functions,

    entropySq μ f = ∫ f² log(f²) dμ − (∫ f² dμ) log(∫ f² dμ).

The definition uses Mathlib's `0 * log 0 = 0` convention. As with any real
Bochner integral, the definition alone does not assert finiteness. The new
integrability theorem supplies that analytic justification.

The three required, Lean-verified statements are:

- `OperatorDerivativeRewrite.Foundation.integrable_sq_mul_log_of_memLp_four`:
  for any measurable space, finite measure μ, and real function f with
  `MemLp f 4 μ`, the function `ω ↦ (f ω)^2 * Real.log ((f ω)^2)` is integrable.
- `OperatorDerivativeRewrite.Foundation.entropySq_nonneg_of_memLp_four`:
  for a probability measure μ and `MemLp f 4 μ`, `0 ≤ entropySq μ f`.
- `OperatorDerivativeRewrite.Foundation.GaussianCore.polynomial_sq_mul_log_integrable`:
  for every real polynomial p, `x ↦ (p.eval x)^2 * Real.log ((p.eval x)^2)`
  is integrable under the existing standard Gaussian measure `GaussianCore.γ`.

No entropy-integrability assumption or positivity assumption on f is added.
The proofs also apply to functions vanishing on positive-measure sets and to
the zero polynomial.

The integrability proof uses Mathlib's nonnegative
`InformationTheory.klFun r = r * Real.log r + 1 - r`.
The new `klFun_le_one_add_sq` proves `klFun r ≤ 1 + r²` for r ≥ 0, with a
separate zero case and the genuine estimate `log r ≤ r - 1` for positive r.
Existing Hölder (`mul_L4_memLp_two`) gives f² in L² and hence f⁴ integrable;
finite-measure exponent comparison gives f² integrable. These facts provide
an integrable majorant for `klFun (f²)`. Subtracting 1 and adding f² proves
integrability of f² log(f²). Jensen's theorem `ConvexOn.map_integral_le`,
using `Real.convexOn_mul_log`, then proves nonnegative square entropy.

Supporting declarations are `entropySq_congr` (a.e. invariance),
`entropySq_zero` (zero entropy for zero under any measure), and
`entropySq_const` (zero entropy for every constant on a probability space).
Together with the definition, the majorant, and the three required results,
all eight declarations are queried in `Foundation/AxiomAudit.lean`.
The module is imported by `OperatorDerivativeRewrite.lean`.

Verification: targeted Lean checking of the new module passed with no errors
or warnings. The complete `lake build` passed (3372 jobs). Fresh execution of
`lake env lean Foundation/AxiomAudit.lean` passed with 722 reports covering
721 distinct declarations. Each of the eight new declarations reports exactly
`{propext, Classical.choice, Quot.sound}`; the complete audit has the same
union. There is no `sorryAx`, custom axiom, or unchecked proof step.
Elaborated `#check @...` statements confirm the hypotheses recorded above.

M1 is complete. This milestone does not establish log-Sobolev, Fisher decay,
a semigroup, or finiteness for every L² function. The original Gaussian
log-Sobolev axiom has not been replaced. Later milestones in the plan remain
open. No external dependency, original manuscript change, or alteration of
an existing theorem statement is part of this milestone.

## Gaussian Mehler M2a: concrete one-dimensional OU kernels (2026-10-11)

Starting verified commit: `62546acb0d3f81a49d5b09613b32e1fcf39f6bf6`.
Implemented `Foundation/GaussianMehler.lean`, namespace
`OperatorDerivativeRewrite.Foundation.GaussianMehler`.

### Scope and exact statements

The measure `γ` is the existing `GaussianCore.γ = gaussianReal 0 1`,
with variance one. The actual definition is

```lean
mehler (t : ℝ) (f : ℝ → ℝ) (x : ℝ) :=
  ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-2 * t)) * y) ∂γ
```

The useful analytic class is specified by `hf : Continuous f` and a real
bound `hM : ∀ z, ‖f z‖ ≤ M`. No smoothness or prescribed derivative is
required. A second function g has the analogous continuity and bound
hypotheses where needed. The mathematical statements of the declarations are:

- `one_sub_exp_nonneg (t) (ht : 0 ≤ t)`: `0 ≤ 1 - exp(-2*t)`.
- `integrable_comp_of_bounded`: for any finite measure μ, measurable real
  f bounded in norm, and measurable g into ℝ, `f ∘ g` is μ-integrable.
  This is an integrability conclusion, not an assumed integrability field.
- `kernel_integrable hf hM t x`: the actual Mehler integrand is γ-integrable.
- `mehler_zero (f)`: `mehler 0 f = f`. No regularity is needed here:
  at zero time the integrand is genuinely constant in y.
- `mehler_const (t c)`: `mehler t (fun _ => c) = fun _ => c`.
- `mehler_mono hf hg hM hN hfg t x`: from `∀ z, f z ≤ g z`,
  `mehler t f x ≤ mehler t g x`, with both integrands proved integrable.
- `mehler_nonneg hf hM hpos t x`: from `∀ z, 0 ≤ f z`,
  `0 ≤ mehler t f x`.
- `mehler_pos hf hM hpos t x`: from `∀ z, 0 < f z`,
  `0 < mehler t f x`; full support of the positive integrand and γ(ℝ)=1
  give strict positivity. There is no assumed uniform positive lower bound.
- `mehler_norm_le hM t x`: `‖mehler t f x‖ ≤ M`.
- `mehler_continuous hf hM t`: `Continuous (mehler t f)`.
- `mehler_integrable hf hM t`: `Integrable (mehler t f) γ`.
- `gaussian_combination_map (a b)`: the map `(x,y) ↦ a*x+b*y` sends
  γ×γ to `gaussianReal 0 (a²+b²)`, with nonnegative variance represented
  explicitly in ℝ≥0. This includes degenerate choices of a and b.
- `kernel_map (t) (ht : 0 ≤ t)`: the Mehler mixing map sends γ×γ to γ.
- `integral_mehler hf hM t ht`: `∫ x, mehler t f x ∂γ = ∫ x, f x ∂γ`.
- `mehler_compose s t hs ht hf hM`: for `0 ≤ s` and `0 ≤ t`,
  `mehler (s+t) f = mehler s (mehler t f)` as functions on ℝ.
- `mehler_tendsto_mean hf hM x`:
  `Tendsto (fun t => mehler t f x) atTop (𝓝 (∫ y, f y ∂γ))`.

The normalization is exp(-t), variance `1-exp(-2*t)`, and invariant standard
Gaussian variance one. Composition and invariance explicitly require
nonnegative times. Some elementary boundedness/continuity statements are
valid for every real time, but no negative-time OU semigroup is asserted.

### Proof dependencies and source compatibility

The pinned upstream implementation was inspected before the port:
[markov-semigroups, Euclidean.lean at acf6491](https://github.com/mrdouglasny/markov-semigroups/blob/acf649108ea2222f4a8544a2782f448cb502492a/MarkovSemigroups/Instances/WorkInProgress/Euclidean.lean).
Its concrete namespace is `Gaussian1D` (rather than a standalone Gaussian1D
file). Reused source arguments are `ouSemigroup`, `ou_kernel_map`,
`ouSemigroup_compose`, value boundedness, and the pointwise dominated
convergence step inside `ouSemigroup_ergodic`. The upstream `IsCore` smoothness
conditions are not used: these particular arguments need only bounded
continuity. The composition proof is a source-level port with attribution.
The file retains Michael R. Douglas's copyright notice; the applicable Apache
2.0 license is included at `LICENSES/Apache-2.0.txt`.

Upstream pins Lean v4.30.0. The port is verified against our unchanged
Lean v4.34.1 and Mathlib lock
`d13f23b723b8a846827a245b89c10fc7d3f11612`. A concrete API migration was needed:
`gaussianReal_add_gaussianReal_of_indepFun` now takes `HasLaw` arguments,
where the pinned upstream proof passed their `.map_eq` equalities. Variance
constructor coercions were checked explicitly. No upstream abstract
semigroup classes, axioms, package dependencies, or derivative results are
imported. This verifies the local port, not the whole upstream repository.

Mathlib supplies `gaussianReal_const_mul`,
`gaussianReal_add_gaussianReal_of_indepFun`, `indepFun_prod`, `integral_map`,
`integral_prod`, bounded integral estimates, and
`tendsto_integral_filter_of_dominated_convergence`.
Constant domination proves each kernel and product integrand integrable.
Invariance follows from the Gaussian mixing law and Fubini. Composition
compares the laws of `exp(-t)*sqrt(1-exp(-2*s))*Y + sqrt(1-exp(-2*t))*Z`
and `sqrt(1-exp(-2*(s+t)))*Y`; their variances coincide. Continuity and the
pointwise limit follow from dominated convergence with majorant M.

### Verification and remaining obligations

All seven requested M2a targets are established on the stated bounded
continuous class. All 18 declarations in this module, including the measure
abbreviation and kernel definition, have transitive `#print axioms` queries
in `Foundation/AxiomAudit.lean`. The root module imports the new module.
Final verification: the complete `lake build` passed (3373 jobs), with no
warnings from the new module. The pre-existing `Foundation.Adjoint` unused
section-variable warnings remain. Fresh `lake env lean Foundation/AxiomAudit.lean`
passed with 740 reports for 739 distinct declarations. Every new declaration
reports exactly `{propext, Classical.choice, Quot.sound}`; the complete audit
has the same union, with no `sorryAx` or custom axiom. Fresh elaborated
`#check @...` queries for all 18 declarations also passed. The ignored
transcripts are `.lake/build/gaussian-mehler-axioms.log` and
`.lake/build/gaussian-mehler-statements.log`. A source scan found no axioms,
`unsafe`, `sorry`, or `admit` in the new module. Original source SHA256 hashes
match the previous milestone, and the dependency configuration and lockfile
have no diff.

M2a does not assert an L²-class extension or strong continuity in L².
M2b (actual spatial differentiation and weighted Fisher-information decay),
M3 (entropy dissipation), and M4 (Gaussian log-Sobolev) remain unimplemented.
The legacy log-Sobolev axiom is not discharged by these kernel properties.
No assertion of a general abstract curvature-dimension theorem follows.
The original manuscripts, existing theorem statements, dependency lockfile,
and the two pre-existing untracked audit/plan documents are preserved.
