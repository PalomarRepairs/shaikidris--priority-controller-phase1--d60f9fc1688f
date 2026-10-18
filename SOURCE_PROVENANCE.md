# Source and attribution

This is a substantive Lean proof library extracted from the author's
priority-controller research development. The manuscript is Idris Ali Shaik,
*Polynomial Fault Detection Without Bounded Width: Exact Reachable Sets in
Priority Controllers*, version 1.0,
[DOI 10.5281/zenodo.23400057](https://zenodo.org/records/23400057).
Each entry's metadata identifies its selected manuscript statements and scope.
The K00 encoded-machine bridge supplies additional resource-respecting
infrastructure; it does not by itself establish membership of a concrete
encoded detector language in a conventional complexity class.

The source manifest records the 921 extracted research modules, their
original SHA-256 digests, and the ported proof-library digests. Research commit
`4fa94a30c6fb3de154f65ba29a70fdb0e6e95172` identifies the repository base.
The audited local source snapshot also contains work outside that commit, so
that commit alone does not reproduce this extraction. The per-file manifest
identifies the actual source input.

The original proof development used Lean 4.33.0. This package uses Lean
4.35.0-rc3 and the complete canonical Mathlib dependency graph recorded in
`lake-manifest.json`. The compatibility port introduces Lean module visibility,
updates proof APIs, and partitions the original large `RawTypedCopy` owner
among its existing module and two imported parts.

Clauses retain the original ordered lists of variable/polarity pairs. Formula
rows retain their array positions, including duplicates. The existing CNF
owner defines `Controller.CNF.OrderedFormula` and proves an equivalence with
Lean's packed standard CNF. Both round trips, row contents and count, literal
counts and satisfaction are proved. The standard LRAT checker receives the
explicit packed conversion. This interoperability operation is separate from
the execution models used for resource bounds.

Author-owned extracted code is licensed under Apache-2.0 with the author's
approval. `Controller/CNF/Basic.lean` adapts the ordered-list CNF API from Lean
4.33.0, copyright 2024 Lean FRO, LLC, authored by Kim Morrison, under Apache-2.0.
Its attribution is retained in the file and `NOTICE`. Lean, Mathlib and their
other dependencies retain their respective licences.

The recorded development used OpenAI Codex and Claude Code under the author's
direction, including GPT-6 and Claude Opus 5.5. These identities are an inspected
provenance account, not a complete usage log. The source manuscript supplied
the mathematical model and proof arguments according to the research plan.
The DOI edition appeared after the initial Lean proofs; its publication date
is not evidence of public precedence over those proofs. No independent human
review or Palomar registration is asserted by this source account.
