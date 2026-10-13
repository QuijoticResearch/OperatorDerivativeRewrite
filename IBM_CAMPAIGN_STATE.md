# Focused IBM campaign state — 2026-10-13

Initial verified HEAD: 473ced866318727d4fc372410aee7c6210415048. Working tree initially contained the same twelve unrelated untracked documents and no tracked changes.

Verified incoming foundation: IBMSourceLaws has actual independent scenery and clock coordinate families, exact two-sided covariance, Brownian finite-dimensional laws on both scenery halves and clock, and independence. The families are not yet continuous or jointly measurable in time/sample.

Active: prove continuous-path composition under explicit independently stated measurable path maps, and prove that genuine coordinate modifications with continuous paths yield measurable path maps and preserve laws. Exact-time path modification existence remains an analytic obligation; no path is defined by asserting continuity.

Pending: construct such modifications from verified Brownian coordinate laws; actual IBM random-time composition on them; conditional mixture, moments, covariance and scaling; mollified scenery; local-time Ito-Tanaka; first-chaos singular infrastructure. Manuscript statements remain UNVERIFIED until proved in Lean.

Preservation: no source manuscript edits, dependency changes, unrelated-document staging, reset or push. Every accepted milestone requires target compilation, full build, explicit types, transitive axiom audit with only propext/Classical.choice/Quot.sound, mathematical scope report, and commit.

## Conditional continuous IBM composition milestone

`Foundation/IBMContinuousComposition.lean` supplies an actual pointwise process on the product `SampleSpace × SampleSpace` from independently supplied measurable path-valued maps `X : SampleSpace → C(ℝ,ℝ)` and `Y : SampleSpace → C(ℝ≥0,ℝ)`. `path` is the continuous path t ↦ X(ωX)(|Y(ωY)(t)|); `value` is its evaluation. It proves pointwise path continuity, one-time measurability, joint time/sample measurability, independence of the entire supplied source paths on the actual product measure, and the zero-time identity when supplied paths vanish at zero. The assumptions are exactly path-map measurability, with optional zero values; no IBM law or moment is smuggled into the definitions.

`Foundation/IBMModificationBridge.lean` proves that a coordinate family with continuous sample paths and measurable deterministic-time coordinates defines a measurable `C(ℝ,ℝ)` or `C(ℝ≥0,ℝ)` random path. When each coordinate is an actual a.e. modification of `IBMSourceLaws.sceneryBase` or the verified `GaussianTimeProcess.process`, the new path keeps the one-time source law. The resulting scenery and clock path-valued variables are independent on the actual product measure. The module does not assert that these continuous modifications already exist; construction from the incoming Gaussian coordinate sources remains the central analytic obligation.

Target builds passed for both modules. Full Lake build: 4205 jobs. All 18 new public declarations have explicit type checks. Complete transitive axiom audit: 3171 declarations, exactly propext, Classical.choice, Quot.sound. Logs `.lake/campaign-ibm/02-*` and `03-*`. No prior theorem body, original manuscript or dependency pin changed.

### Exact declaration locations

Names have prefix `OperatorDerivativeRewrite.Foundation.`.
- `Foundation/IBMContinuousComposition.lean`:
  - `IBMContinuousComposition.path` — line 17
  - `IBMContinuousComposition.value` — line 21
  - `IBMContinuousComposition.path_continuous` — line 23
  - `IBMContinuousComposition.value_eq` — line 26
  - `IBMContinuousComposition.sources_independent` — line 29
  - `IBMContinuousComposition.value_measurable` — line 34
  - `IBMContinuousComposition.path_measurable` — line 42
  - `IBMContinuousComposition.value_jointly_measurable` — line 47
  - `IBMContinuousComposition.value_zero` — line 52
- `Foundation/IBMModificationBridge.lean`:
  - `IBMModificationBridge.sceneryPath` — line 13
  - `IBMModificationBridge.clockPath` — line 16
  - `IBMModificationBridge.sceneryPath_measurable` — line 19
  - `IBMModificationBridge.clockPath_measurable` — line 23
  - `IBMModificationBridge.sceneryPath_apply` — line 28
  - `IBMModificationBridge.clockPath_apply` — line 31
  - `IBMModificationBridge.scenery_modified_law` — line 35
  - `IBMModificationBridge.clock_modified_law` — line 44
  - `IBMModificationBridge.modified_sources_independent` — line 52
