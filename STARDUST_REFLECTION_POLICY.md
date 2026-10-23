# Periodic mathematical reflection and documentation

User directive received October22,2026. This is permanent supporting workflow,
not a research campaign and not a change to STARDUST_CAMPAIGN_QUEUE.md.
IBM remains active. All mathematical source, domain, audit, manuscript-integrity,
Git and PRIVATE main/research backup gates continue unchanged.

## Timing and admission

October22 clarification: at most ONE opportunistic reflection/housekeeping
session per America/New_York calendar day. Before admission, check both
last_reflection_date and all historical sessions/reservations. Reserve the local
date before any work; a partial or budget-limited session consumes that date,
even if time remains. Record the most recent reflection date at closure.
Never interrupt an active proof or verification cycle. A scheduled check is
only an eligibility check, not an appointment. If no suitable natural verified
checkpoint occurs, skip that day's session; no forced work or make-up sessions.
Earlier multiple-session records are preserved as historical accounting and
do not authorize additional sessions under this amended rule.

Spend AT MOST45minutes TOTAL per America/New_York calendar day across ALL
reflection, synthesis, documentation, associated verification and housekeeping
sessions. This is a ceiling, not a daily target. Skip a day/session when nothing
mathematically worthwhile needs attention. Work only at a natural completed,
audited checkpoint; never interrupt or restart an active proof or investigation.

Use the terminal system clock, not token counts or discovery counts. Consult
STARDUST_REFLECTION_SESSIONS.json before admission. Sum completed charges for
the local date and any outstanding reservation; no concurrent reflection and
no second session on a date already used.
Reserve the remaining allowance and record start UTC, local date and deadline
before work. Check actual elapsed time after verification/research stages.
Count setup and all closure work. Reserve enough time for gates before editing;
avoid starting a proof near the deadline. A session spanning local midnight
must charge each day's actual overlap separately, never borrow tomorrow's time.

At close, charge actual elapsed wall time, release the unused reservation, and
record completion/evidence in the ledger. A stale active reservation is not
free time: inspect its actual run state; absent verified closure, conservatively
retain its reserved charge for that date. Do not interrupt a live process to
perform reflection. The authoritative queue can be changed only by explicit
user authorization.

Git/sync closure may use a small explicit finalization allowance recorded in
the committed accounting entry, with an exact terminal receipt under .lake/.
Until that receipt proves closure, no new reflection session is admitted.
Reconcile any unused allowance (or excess observed closure time) from that
receipt before the next admission; if evidence is missing, keep the reservation.

## Mathematical purpose

Review a SMALL, meaningful part of the cumulative library rather than ingesting
all manuscripts or producing documentation for its own sake. Look for exact
cross-campaign identities, transferable hypotheses, stronger generalizations,
resolved old obstructions and formerly unsuccessful strategies made viable by
new machinery. State a concrete theorem, reduction or missing premise for each
opportunity. Do not manufacture a connection from shared vocabulary.

Distinguish a standard theorem, a theorem verified here, a problem open in this
repository, a genuinely established external open problem, and a question whose
literature status is unchecked. Do not undertake lengthy novelty surveys or
start substantial new campaigns. Test a precise connection in Lean when feasible
within the shared budget; preserve verified results and meaningful unresolved
obligations. Record candidate work for its proper future campaign.

Preserve mathematical experience: intermediate reductions, necessary hypotheses,
counterexamples, valid unsuccessful approaches and their reasons, and occasions
when later work resolves an earlier obstruction. A compiler or tactic failure
is not a mathematical obstruction. Prefer the mathematical lesson over routine
elaboration diagnostics. Optimize for understanding and verified progress,
not theorem, commit or document counts.

## Maintained artifacts

- README.md: concise public-facing entry point; approximately5–10 significant
  results with exact declarations, domains, verified status and detailed links.
  Explain purpose, transparent/reproducible sharing philosophy, verification and
  major directions. No unsupported novelty, publication or RH claims; no log
  of each commit. Public-facing prose never changes repository privacy/license.
- STARDUST_BLUEPRINT.md: navigable curated mathematical blueprint, definitions,
  theorem statements, actual reuse relationships and remaining obligations.
  Identify conceptual links separately from literal Lean import dependencies.
- STARDUST_MATHEMATICAL_COMMENTARY.md: concise explanations of constructions,
  obstacles, successful repairs and precise new opportunities.
- manuscripts/: canonical LaTeX drafts and corresponding private PDFs together,
  indexed by manuscripts/INDEX.md. Follow the compilation policy below.
- docs/papers/: supporting Markdown exposition, theorem statements aligned
  with Lean and explicit PROVED/OPEN/CONJECTURAL status. Do not rewrite original
  manuscripts or assert publication-level novelty without evidence.
- STARDUST_REFLECTION_LOG.md and PROJECT_STARDUST_REPORT.md: bounded session
  findings, source/declaration references, meaningful lessons and follow-ups.
- STARDUST_REFLECTION_SESSIONS.json: shared daily accounting and reservations.

Historical snapshots are evidence of earlier understanding, not controlling
current theorem status. Preserve originals and ResearchSources byte-for-byte;
do not rename, delete or commit archive files. Keep unrelated drafts untouched.

## LaTeX manuscript and PDF compilation

Maintain mathematical paper drafts as main.tex and main.pdf in a clearly named
subdirectory of manuscripts/. Preserve original ResearchSources manuscripts.
The index lists title, source/PDF locations, verified mathematical scope,
latest revision and compilation status. Markdown notes may link to the canonical
LaTeX draft; they are not a competing unsynchronized manuscript source.

Recompile after substantive manuscript changes, within the SAME45minute daily
allowance. Use the installed local toolchain, not an external compiler or upload.
The verified local route is tools/compile_stardust_manuscript.py with MiKTeX
pdflatex; package installation and shell escape are disabled. Run two passes,
check final references/labels and layout diagnostics, render and actually inspect
every page for notation, clipping, spacing and readability. Never call a stale
or uninspected PDF current. Preserve every failed compilation/layout log and
repair errors only within the remaining budget. If time expires, retain source
and logs, mark compilation PENDING in the index, and resume at a later eligible
checkpoint. A successful compiler exit alone is not complete PDF verification.

Keep source/PDF hashes and build metadata in build-status.json and a separate
visual review receipt. Keep auxiliary builds/rendered pages ignored and organized;
retain source, current PDF, index and meaningful compilation logs. No unnecessary
cleanup of unrelated caches. All draft claims must match exact verified Lean
statements/domains; speculative material must be labeled explicitly.

All artifacts remain private. The existing explicitly authorized PRIVATE Git
checkpoint backup remains permitted; no public release, external publication,
third-party upload or remote compilation is authorized by this workflow.
See manuscripts/README.md for local commands and manuscript freshness checks.

## Verification and recurrence

Follow STARDUST_BUILD_OPTIMIZATION.md and STARDUST_SYNC.md. Full root build,
complete transitive safe-Foundation axiom audit, actual complete public-type/
source review, meaningful independent checks, source/manuscript hash checks,
explicit Git commit, exact receipt and verified PRIVATE main/research refs
remain the checkpoint gates. No sorry, new mathematical axioms, suppressed
errors or weaker statement presented as a stronger result. Documentation-only
reuse of previous audit evidence requires exact input identity as specified
in the existing build policy; it never approves changed mathematical sources.

The autonomous loop consults this policy at natural checkpoints. A quiet daily
thread heartbeat checks eligibility; if a proof or verification cycle is active,
the date was already used, eligibility is
uncertain, the daily budget is reserved/exhausted, or no useful task exists,
skip without changing campaign priority. Do not create a new research goal,
parallel research session or duplicate automation. Notify only for a meaningful
discovery, completed substantive update, failure or needed user action.

Source: the user's attached “Project Stardust — Periodic Mathematical Reflection
and Housekeeping” brief. Its content is preserved separately in
docs/STARDUST_REFLECTION_USER_BRIEF.md. The operational accounting and artifact
choices above implement that brief without changing its mathematical priorities.
