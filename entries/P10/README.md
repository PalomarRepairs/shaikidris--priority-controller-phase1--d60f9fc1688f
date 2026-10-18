# Encoded simulation and resource-respecting reductions

The K00 library connects executed native programs to encoded binary machines
and supports resource-respecting composition. Its full contract contains 39
supporting declarations. The entry selects six principal theorems from
[Solution.lean](../../Phase1/P10/Solution.lean).

The native simulation requires an executed image constructor and a bound on
the native execution. It charges the constructor and the intermediate encoded
image. The space results use a literal finite-control tape transition model,
with blank initial work tapes and a visited-cell bound. The time realizations
produce Mathlib `FinTM2` witnesses. These statements do not supply missing
constructors for a particular detector or classify its encoded language.

The six arguments are as follows.

1. `ImageCanonical.decoded_execution` proves that accepted machine-image
   parsing determines the original encoding. The encoded interpreter execution
   can therefore be transported to every accepted input, with the same explicit
   time and peak-space polynomials.
2. `NativeCompilation.tm_polytime` composes the executed constructor with the
   cold interpreter. The constructor's output-length bound controls the image
   length; native storage-growth bounds eliminate uncharged peak parameters.
   Polynomial monotonicity bounds the composition, which is then realized as
   a finite TM2 computation.
3. `SpaceTapeBridge.composed` applies the virtual-input composition construction
   and its logarithmic workspace bound, then boots the work tapes from blank
   input and simulates every source step. Its explicit interval capacity
   bounds the visited work positions.
4. `SpaceTapeErasure.logspace` erases allocation bookkeeping from configurations
   while preserving every literal transition. The allocation invariant covers
   all visited work positions, and the finite interval cardinality gives the
   stated logarithmic cell count.
5. `ParameterReduction.compose` combines actual machine executions and
   language equivalences. A computable finite-prefix maximum majorizes the
   second parameter bound, so neither parameter-growth function needs a
   monotonicity assumption.
6. `ParameterTM.realization` extracts finite control from the computation
   witness and fixes one TM2 and two alphabet equivalences before quantifying
   over inputs. Its output execution has the supplied parameter-dependent
   time bound.

The custom encodings, cold-machine constants and composition witnesses are
formal statements of this development. Their mechanisms are standard machine
simulation and reduction composition; this entry makes no novelty claim for
those general principles. [formalization.yaml](formalization.yaml) distinguishes
this infrastructure from the controller manuscript used as background.
