# Exact fault images in priority controllers

This Lean development studies a finite priority controller with independent
enable and request bits. Its selector follows the literal XOR-mask recurrence;
observations read the final qualifier vector before any channel encoder.

The P01 comparison surface proves that an activated drive-one first-stage
bridge has healthy eligible set equal to its target singleton and faulty set
equal to any admissible nonempty set. A single bus requires target membership.
Every admitted pair has a primary-input realization. Drive zero is undetectable.
Detection through any finite family of Boolean qualifier observations is
therefore equivalent to a discrepancy on an admissible set.

The other selected physical results show that proper-coordinate relations
cannot express global nonemptiness and classify a specified final-qualifier
stuck-at occurrence. The latter fault leaves all selector occurrences unchanged.

Read [the Challenge](Phase1/P01/Challenge.lean) for the explicit equations and
six formal statements, [the Solution](Phase1/P01/Solution.lean) for their proof
owners, and [the Comparator configuration](entries/P01/comparator.json) for the
exact selection. [formalization.yaml](formalization.yaml) records sources,
scope, authorship, automation and review status.

The informal source is Idris Ali Shaik, *Polynomial Fault Detection Without
Bounded Width: Exact Reachable Sets in Priority Controllers*, version 1.0,
[DOI 10.5281/zenodo.23400057](https://zenodo.org/records/23400057), Section 3
and statements 4.1–4.4. The selected entry asserts no algorithmic complexity,
arbitrary-CNF recognition or completion of every theorem in that manuscript.

The source library also contains the accepted supplied-decoder, certificate
and encoded-machine developments. [Their ten entry surfaces](ENTRIES.md) are separately selected;
they are not implicit claims of the P01 Comparator.

The project uses Lean 4.35.0-rc3 and canonical Mathlib at the exact revision in
the Lake manifest. Build the physical entry with:

```sh
lake build Phase1.P01.Challenge Phase1.P01.Solution
lake comparator --config entries/P01/comparator.json
```

The proofs were developed with AI assistance under the author's direction.
No independent human review or Palomar registration is claimed. Author-owned
source is licensed under [Apache-2.0](LICENSE); dependency licences and notices
remain applicable.
