import SPR
import Lean.Util.CollectAxioms

/-!
# Build-time axiom audit

This module is a default library root. Every theorem under `SPR` is
checked transitively; an unexpected axiom causes `lake build` to fail.
The proof uses only the standard propositional-extensionality, choice and
quotient axioms. No external process supplies a proof to the kernel.
-/

#check SPR.N5.Direct.robustSPR
#print axioms SPR.N5.Direct.robustSPR

set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut checked := 0
  for (name, info) in env.constants.toList do
    if (`SPR).isPrefixOf name && info.isTheorem then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Unexpected axiom {axiomName} in {name}"
      checked := checked + 1
  if checked < 426 then
    throwError "Incomplete proof import: audited only {checked} theorems"
  Lean.logInfo m!"SPR axiom audit passed: {checked} theorems; only propext, Classical.choice, Quot.sound"
