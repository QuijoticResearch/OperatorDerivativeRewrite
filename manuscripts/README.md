# Private mathematical manuscripts

[The manuscript index](INDEX.md) lists every maintained paper, its source/PDF,
mathematical verification boundary, latest revision and build/review status.
Canonical drafts live in named subdirectories as main.tex and main.pdf together.
Original ResearchSources files are never edited or compiled in place.

The verified native Windows compiler is MiKTeX-pdfTeX4.23 (MiKTeX25.12), found at
`C:/Users/ramir/AppData/Local/Programs/MiKTeX/miktex/bin/x64/pdflatex.exe`.
No Lean/Mathlib toolchain change is involved. Local font/cache access may require
the existing host permission; this is not authorization for remote compilation.

From the repository root:

```powershell
& 'C:/Users/ramir/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/python.exe' -X utf8 `
  tools/compile_stardust_manuscript.py manuscripts/ibm-stochastic-associativity `
  --compiler 'C:/Users/ramir/AppData/Local/Programs/MiKTeX/miktex/bin/x64/pdflatex.exe'
```

The helper runs two pdflatex passes, with package installation and shell escape
disabled. It keeps timestamped stdout/TeX logs and per-attempt JSON metadata in
logs/, including failures. It rejects unresolved references/citations, changed
labels requiring another pass, multiply defined labels and overfull boxes.
Only a successful diagnostic check copies the PDF alongside its source.
build-status.json pins source/PDF hashes and marks visual review as still needed.

Render the current PDF with local Poppler and inspect EVERY page:

```powershell
pdftoppm -r 110 -png manuscripts/ibm-stochastic-associativity/main.pdf `
  manuscripts/ibm-stochastic-associativity/rendered/page
```

Create rendered/ if needed. After inspection, write visual-review.json with the
reviewed source/PDF hashes, page count, review timestamp, checked notation and
reference status. A current verified PDF requires source hash, PDF hash,
successful build metadata AND visual-review receipt to agree. Internal equation
and theorem references must resolve. Source theorem references must match Lean.

Substantive edits invalidate freshness until recompiled/reviewed. Preserve a
failed source and all logs; an older retained PDF is not a successful build of
the new source. If the shared housekeeping budget expires, mark PENDING in the
index and leave the source intact. Do not silently substitute Markdown or a
different PDF-generation engine for the maintained LaTeX manuscript.

All work, including error repair, PDF review, verification and Git/private
closure, shares the existing45minute DAILY maximum. Read
[the policy](../STARDUST_REFLECTION_POLICY.md) and
[daily accounting](../STARDUST_REFLECTION_SESSIONS.json) first. Auxiliary build/
and rendered/ files are ignored. Keep current .tex/.pdf and meaningful logs.
No external upload/publication is authorized; existing explicitly authorized
PRIVATE Git checkpoint backup remains the only configured remote destination.
