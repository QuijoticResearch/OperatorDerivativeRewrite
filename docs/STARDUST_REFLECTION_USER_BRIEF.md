# Project Stardust — Periodic Mathematical Reflection and Housekeeping

Maintain a lightweight, recurring process of mathematical reflection, synthesis, discovery, and documentation alongside the autonomous research program.

**Time budget: Up to 45 minutes per day, total.** This is a maximum, not a target. Perform the work at natural verified checkpoints, without interrupting active proofs or investigations.

The primary purpose is not administrative housekeeping. It is to **extract additional mathematical value from the research already performed**, preserve research experience, identify unexpected connections, and recognize new opportunities for discovery.

## 1. Mathematical Reflection and Cross-Library Discovery

Periodically step back from the immediate theorem being proved and examine the cumulative verified library as a whole.

Investigate:

- Connections between different research campaigns, including operator derivatives, Gaussian calculus, pseudoprocesses, IBM, higher-order heat flows, and subsequent mathematical developments.
- Shared mathematical structures that might admit a more general theorem.
- Previously established results that can strengthen, simplify, or generalize results in another branch.
- Verified counterexamples and obstructions that reveal common limitations or suggest alternative constructions.
- Previously unsuccessful proof strategies that may now be viable because new machinery exists.
- Mathematical patterns, identities, or abstractions that were not apparent when individual results were first developed.

**Do not manufacture connections.** Require a precise mathematical relationship or a plausible, explicitly stated theorem to investigate.

Where a promising connection is found, formulate a concrete conjecture, reduction, or proof obligation.

When feasible within the time budget, test the idea in Lean. Preserve verified results and meaningful unresolved obligations.

## 2. Open Problems and New Research Opportunities

Consider whether the cumulative library provides new leverage on established open mathematical problems or meaningful unresolved questions emerging from our own research.

Identify promising opportunities based on:

- Existing verified mathematical infrastructure.
- Reusable lemmas and proof strategies.
- Previously encountered obstructions.
- Potential cross-disciplinary applications.
- Mathematical significance and tractability.

Distinguish genuinely open problems from established results, known generalizations, and problems whose status has not been independently checked.

Do not conduct lengthy novelty surveys or launch substantial new campaigns during housekeeping.

Record promising ideas with their mathematical motivation, relevant Lean declarations, and potential next steps.

**Preserve opportunities for later exploration rather than distracting the active research campaign.**

Do not modify the authoritative campaign queue without explicit authorization.

## 3. Preserve Mathematical Research Experience

Treat successful proofs, verified counterexamples, and mathematically valid unsuccessful approaches as valuable research artifacts.

Preserve:

- Verified intermediate reductions.
- Missing assumptions discovered through failed approaches.
- Counterexamples and impossibility results.
- Unresolved mathematical obligations.
- Alternative proof strategies and why they were abandoned.
- Cases where a previous obstruction was subsequently resolved.
- Connections between earlier failures and later mathematical successes.

Distinguish Lean compilation failures from actual mathematical obstructions.

Prefer preserving meaningful mathematical experience over recording routine tactic failures.

The objective is not merely to remember what was proved, but to preserve **what the research process learned**.

## 4. README.md — Public Overview

Maintain the README as the public entry point to Project Stardust.

Include a curated selection of approximately 5–10 of the strongest mathematical results, chosen for significance rather than recency.

Provide concise explanations, exact Lean declaration references, verified status, and links to detailed documentation.

Explain the project's purpose, open-source philosophy, verification standards, and major research directions.

Highlight meaningful cross-campaign connections when they have been established.

Avoid unsupported novelty claims and promotional exaggeration.

Do not turn the README into a commit log.

## 5. Lean Blueprint

Maintain a navigable blueprint of the verified mathematical development.

Record major definitions, theorem statements, dependency relationships, proof obligations, and connections between mathematical branches.

Identify important structural relationships and generalizations suggested by the theorem graph.

The blueprint should help both humans and future research agents understand how the mathematical infrastructure fits together.

## 6. Mathematical Commentary

Maintain concise research commentary explaining:

- Why important constructions work.
- Which mathematical difficulties motivated them.
- How obstructions led to alternative approaches.
- Which results unexpectedly connect different campaigns.
- Which new mathematical questions emerged from completed work.

Emphasize mathematical substance rather than chronological narration.

## 7. Research Paper Drafts

Incrementally organize substantial results into coherent mathematical drafts.

Keep theorem statements, assumptions, domains, and proof explanations aligned with verified Lean declarations.

Clearly distinguish proved results, conjectures, incomplete arguments, and speculative interpretations.

Do not rewrite entire manuscripts after each checkpoint or claim publication-level novelty without evidence.

Preserve all original research manuscripts and ResearchSources unchanged.

## 8. Research Priorities and Verification

Lean source, exact theorem statements, and verified checkpoints remain authoritative.

Apply the established full-build, axiom-audit, independent-check, Git, and private-backup requirements.

Never introduce `sorry`, custom mathematical axioms, or weakened theorem statements disguised as stronger results.

Keep reflection and documentation within the shared 45-minute daily budget.

Do not interrupt an active proof to perform reflection. If nothing meaningful needs attention, skip the session.

Promising new directions should be recorded for future investigation, not automatically pursued at the expense of the existing queue.

## Guiding Principle

**Stardust should periodically examine not only what it has proved, but what its accumulated mathematics and research experience now make possible.**

The goal is to discover connections, identify new opportunities, preserve lessons from unsuccessful approaches, and make the growing library increasingly useful.

Do not optimize merely for theorem count, commit count, or documentation volume.

Optimize for cumulative mathematical understanding, reusable discoveries, and verified progress.

**Explore broadly. Reflect critically. Preserve experience. Prove rigorously.**