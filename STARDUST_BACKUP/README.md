# Project Stardust private backup

This backup-only branch retains the complete verified research tree and history, plus byte-for-byte copies of the read-only manuscript archive, untracked research notes, and active IBM draft sources. The source checkout, branch, index, and manuscript files were not changed to create it.

The verified research baseline is `fa7ebb7d65279a409a5591519b96a1be4d6ab985`. Files in `working-drafts/` are experimental proofs, not a root-audited mathematical checkpoint. Their source hashes and original locations are recorded in `manifest.json`; verification evidence and the research continuation notes are in `verification/`.

To recover ongoing IBM work, restore the draft files to their recorded original `.lake/` locations after checking their hashes. Do not treat draft checks as resolution of IBM F1–F3. The active campaign remains IBM, with the previously recorded successor gates and October 31 stopping date.

Build outputs, downloaded dependencies, portable audit tools, corrupted caches, credentials, and unrelated temporary outputs are excluded. The existing branches and tags retain their original commit IDs. This repository is intended to remain PRIVATE.
