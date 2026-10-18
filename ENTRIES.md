# Selected formalization entries

The ten entries select 76 theorem statements from the Paper A proof library and
its encoded-machine bridge. Their complete source audit covers 109 declarations,
including all 39 K00 obligations. Each entry has its own transparent Challenge,
Solution imports, comparison configuration and source metadata.

| Entry | Scope | Theorems | Metadata |
|---|---|---:|---|
| [P01](Phase1/P01/Challenge.lean) | Exact physical image and observation criterion | 6 | [Metadata](formalization.yaml) |
| [P02](Phase1/P02/Challenge.lean) | Guarded decision and constrained extension | 6 | [Metadata](entries/P02/formalization.yaml) |
| [P03](Phase1/P03/Challenge.lean) | Canonical enumeration, termination and streaming delay | 6 | [Metadata](entries/P03/formalization.yaml) |
| [P04](Phase1/P04/Challenge.lean) | Formula-forest execution and weighted candidate bounds | 2 | [Metadata](entries/P04/formalization.yaml) |
| [P05](Phase1/P05/Challenge.lean) | Dual-Horn and graph-cover representations | 7 | [Metadata](entries/P05/formalization.yaml) |
| [P06](Phase1/P06/Challenge.lean) | Critical sets, query, width and backdoor obstructions | 14 | [Metadata](entries/P06/formalization.yaml) |
| [P07](Phase1/P07/Challenge.lean) | Bounded live conjunction and proper-basis algorithms | 11 | [Metadata](entries/P07/formalization.yaml) |
| [P08](Phase1/P08/Challenge.lean) | Observation projection, producer recovery and typed certificates | 10 | [Metadata](entries/P08/formalization.yaml) |
| [P09](Phase1/P09/Challenge.lean) | Ordinary resolution and observation wrappers | 8 | [Metadata](entries/P09/formalization.yaml) |
| [P10](Phase1/P10/Challenge.lean) | Resource-respecting encoded simulation and reduction composition | 6 | [Metadata](entries/P10/formalization.yaml) |

The detector and enumeration results use the literal, charged native execution
model and supplied decoder evidence. The machine bridge supplies conventional
encoded executions under its stated constructor and resource premises; those
premises remain part of every corresponding theorem. The width obstruction
uses the displayed graph expansion and degree assumptions. Proper-basis
execution does not assert the full-basis hardness classification. Certificate
recovery uses typed payloads and the displayed explicit grammar and checkers.
The selected forest weight theorem bounds feasible true-set weights by a returned
candidate score; it does not certify a maximum-weight physical test.
Resolution claims concern ordinary resolution and the stated inference or
literal-storage measures.

K01 encoded-language membership and the remaining whole-paper tranche are
outside these selections. The six manuscript statements added after the
accepted formalization snapshot are also outside the selected theorem map.

The primary physical entry is described in [the project README](README.md).
[Source provenance](SOURCE_PROVENANCE.md) records the manuscript identity,
authorship, AI assistance and per-file extraction identities.
