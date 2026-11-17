import ContinuousBilinear
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if origin.toString.startsWith "ContinuousBilinear" then
        count := count + 1
        for ax in (← Lean.collectAxioms name).toList do
          unless allowed.contains ax do
            throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Checked axiom dependencies of {count} local declarations."

#print ContinuousBilinear.Targets.IntegerReduction
#print ContinuousBilinear.Targets.CanonicalIntegerUndecidability
#print ContinuousBilinear.Targets.FeedbackExactTransitions
