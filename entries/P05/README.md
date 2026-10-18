# Dual-Horn models and vertex covers

This entry represents dual-Horn assignments and finite graph vertex covers as
physical bridge detections in a finite priority controller. Its seven selected
theorems give the model/detection equivalence, linear counted decoder size,
formula-forest structure, and the cover count and physical realization laws.
Declared unused variables and isolated vertices remain part of the universe.
The count concerns eligible qualifier sets.

The [Challenge](../../Phase1/P05/Challenge.lean) states the seven results and
shows the reduction, graph, CNF and physical definitions. The
[Solution](../../Phase1/P05/Solution.lean) imports their proof owners.
[comparator.json](comparator.json) selects the declarations, and
[formalization.yaml](formalization.yaml) records the manuscript alignment and
attribution. The verifier uses `formalization_metadata_path` to select this
entry's metadata.

From the package root:

```sh
lake build Phase1.P05.Challenge Phase1.P05.Solution
lake comparator --config entries/P05/comparator.json
```

The mathematical source is Theorems 5.2 and 6.4 of Idris Ali Shaik,
*Polynomial Fault Detection Without Bounded Width: Exact Reachable Sets in
Priority Controllers*, [version 1.0](https://zenodo.org/records/23400057).
