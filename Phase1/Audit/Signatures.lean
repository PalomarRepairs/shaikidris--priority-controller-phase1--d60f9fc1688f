module

import Phase1.P01.Solution
import Phase1.P02.Solution
import Phase1.P03.Solution
import Phase1.P04.Solution
import Phase1.P05.Solution
import Phase1.P06.Solution
import Phase1.P07.Solution
import Phase1.P08.Solution
import Phase1.P09.Solution
import Phase1.P10.Solution
import Lean.Util.CollectAxioms
import Lean.Meta.PPGoal

set_option pp.fullNames true
set_option pp.universes true

open Lean Elab Command in
run_cmd do
  let names : List Name := [`Controller.Physical.separated_drive_one_set_pair_image_iff, `Controller.Physical.not_bridgeDetectable_drive_zero, `Controller.Physical.bridge_detectable_iff_exists_output, `Controller.Physical.proper_projection_full, `Controller.Physical.valid_local_relations_accept_zero, `Controller.Physical.stuck_detectable_iff, `Controller.Public.guarded_bridge_detector_correct, `Controller.Public.guarded_bridge_detector_complete, `Controller.Cost.SharedDetectorCold.execution, `Controller.Decoder.DAG.extendSet_some, `Controller.Decoder.DAG.extendSet_none_iff, `Controller.Decoder.DAG.extendSet_exists_iff, `Controller.Cost.Enumeration.execution, `Controller.Cost.Enumeration.results_exact, `Controller.Cost.Enumeration.canonical_result_detects, `Controller.Cost.Enumeration.iterator_delay, `Controller.Cost.Enumeration.delay_bound, `Controller.Cost.Enumeration.program_words_bound, `Controller.Cost.ForestOriginalSemantics.original_physical_execution, `Controller.Optimization.Weights.forest_maximum_weight, `Controller.Reductions.DualHorn.model_bridge_detectable_iff, `Controller.Reductions.DualHorn.decoder_size_linear, `Controller.Reductions.DualHorn.decoder_formulaForest, `Controller.Reductions.coverDAG_size_linear, `Controller.Reductions.cover_detection_count, `Controller.Reductions.cover_physical_detects_only_covers, `Controller.Reductions.cover_realizer_detects_iff, `Controller.Cost.CriticalSets.cycle_complete, `Controller.Cost.CriticalSets.cycle_unique, `Controller.Boundaries.physical_test_list_lower_bound, `Controller.Boundaries.criticalSets_card_one, `Controller.Boundaries.criticalSets_card_many, `Controller.Cost.CriticalSets.critical_complete, `Controller.Boundaries.deterministic_one_bus, `Controller.Boundaries.deterministic_many_buses, `Controller.Boundaries.randomized_mixture_lower_bound, `Controller.Graph.NativeWidth.primal_treewidth_lower, `Controller.Graph.NativeWidth.incidence_treewidth_lower, `Controller.Boundaries.Backdoors.native_backdoor_lower_bound, `Controller.Boundaries.Backdoors.specification_backdoor_lower_bound, `Controller.Graph.CoverCircuit.linear_width_obstruction, `Controller.Decoder.DAG.exists_small_true_support, `Controller.Decoder.DAG.exists_small_target_support, `Controller.Decoder.DAG.expansion_identity, `Controller.Decoder.DAG.global_selector_count, `Controller.Decoder.DAG.cone_expansion_identity, `Controller.Extensions.BoundedNativeComplete.execution, `Controller.Extensions.BoundedNativeComplete.emitted_witness, `Controller.Extensions.BoundedNativeComplete.xp_time, `Controller.Extensions.BoundedNativeComplete.one_and_time, `Controller.Extensions.BoundedNativeComplete.healthy_one_time, `Controller.Extensions.ProperBasisComplete.execution, `Controller.Native.ObservationProjection.observation_projection_of_unit_conflict, `Controller.Native.ObservationProjection.optional_declared_cnf_projection, `Controller.Native.ObservationProjection.selected_declared_cnf_projection, `Controller.Recognition.IntendedDAG.recovery_exact, `Controller.Recognition.GuardedFamily.decodeChecked_sound, `Controller.Recognition.GuardedFamily.decodeChecked_lifting, `Controller.Certificate.Pipeline.runFamily_sat_iff, `Controller.Certificate.Pipeline.runFamily_certified_unsat, `Controller.Certificate.Pipeline.runFamily_sat_sound, `Controller.Certificate.Pipeline.runFamily_unsat_sound, `Controller.Cost.NativeResolution.native_refutation_encoded_cubic, `Controller.Cost.NativeResolution.compactNativeCompile_complete, `Controller.Cost.NativeResolution.compactNativeCompile_checked, `Controller.Cost.NativeResolution.canonical_derived_literal_storage, `Controller.Cost.WrapperResolution.runOptional_complete_cubic, `Controller.Cost.WrapperResolution.runSelected_complete_cubic, `Controller.Cost.WrapperResolution.runOptional_checked, `Controller.Cost.WrapperResolution.runSelected_checked, `Controller.Complexity.Encoding.wordEncoding, `Controller.Complexity.MachineBridge.stateEncoding, `Controller.Complexity.MachineInput.decode_encode, `Controller.Complexity.MachineInput.encode_injective, `Controller.Complexity.MachineInput.encode_length_le, `Controller.Complexity.ImageCanonical.image_inverse, `Controller.Complexity.ColdInterpreter.encoded_execution, `Controller.Complexity.ColdInterpreter.malformed_execution, `Controller.Complexity.NativePolynomial.encoded_execution, `Controller.Complexity.ImageCanonical.decoded_execution, `Controller.Complexity.NativeCompilation.computes, `Controller.Complexity.NativeCompilation.tm_polytime, `Controller.Complexity.StackMachine.Execution.compose, `Controller.Complexity.StackMachine.Computes.compose, `Controller.Complexity.StackMachine.Computes.output_length_le, `Controller.Complexity.StackMachine.Computes.tm_polytime, `Controller.Complexity.NativeCompilation.output_length, `Controller.Complexity.LogSpaceBounds.Computes, `Controller.Complexity.SpaceComposition.computes, `Controller.Complexity.SpaceComposition.exists_program, `Controller.Complexity.SpaceMicroRun.expanded, `Controller.Complexity.SpaceTapeBridge.composed, `Controller.Complexity.SpaceTapeAllocation.logspace, `Controller.Complexity.SpaceTapeErasure.logspace, `Controller.Complexity.TapeTransducer.Machine, `Controller.Complexity.TapeTransducer.projection, `Controller.Complexity.TapeTransducer.Covered.evals, `Controller.Complexity.Constructibility.TimeConstructible, `Controller.Complexity.Constructibility.SpaceConstructible, `Controller.Complexity.Constructibility.time_one, `Controller.Complexity.Constructibility.space_one, `Controller.Complexity.ParameterMajorant.computable, `Controller.Complexity.ParameterMajorant.bounded, `Controller.Complexity.ParameterBounds.composed, `Controller.Complexity.ParameterRuntime.Computes.compose, `Controller.Complexity.ParameterRuntime.Computes.physical, `Controller.Complexity.ParameterReduction.compose, `Controller.Complexity.ParameterReduction.output_size, `Controller.Complexity.ParameterTM.realization]
  let env ← getEnv
  for name in names do
    let info ← getConstInfo name
    let rendered ← liftTermElabM <| do
      return (← Meta.ppExpr info.type).pretty
    let moduleName := match env.getModuleIdxFor? name with
      | some index => env.header.moduleNames[index]!.toString
      | none => "<local>"
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "unapproved axiom {axiomName} in {name}"
    let row := Json.mkObj [
      ("declaration", toJson name.toString), ("module", toJson moduleName),
      ("type", toJson rendered), ("is_theorem", toJson info.isTheorem),
      ("axioms", toJson (axioms.toList.map Name.toString))]
    logInfo m!"SCOPE_RECORD: {row.compress}"
  logInfo m!"SCOPE_PASS: {names.length} declarations"
