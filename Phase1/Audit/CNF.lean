module

import Controller.CNF.Basic
import Lean.Util.CollectAxioms
import Lean.Meta.PPGoal

set_option pp.fullNames true
set_option pp.universes true

open Lean Elab Command in
run_cmd do
  let names : List Name := [`Controller.CNF.OrderedFormula.list_roundtrip, `Controller.CNF.OrderedFormula.std_roundtrip, `Controller.CNF.OrderedFormula.row_count, `Controller.CNF.OrderedFormula.row_literals, `Controller.CNF.OrderedFormula.clause_size, `Controller.CNF.OrderedFormula.literal_count, `Controller.CNF.OrderedFormula.clause_sat, `Controller.CNF.OrderedFormula.formula_sat]
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
