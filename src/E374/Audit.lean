import E374.D3
import E374.D3Asymp
import E374.D4
import E374.D5Main
import E374.EBounds
import E374.EBoundsWeil

/-!
# Axiom audit for the D3 / D4 / D5 order-of-growth package

Every headline theorem below takes its analytic inputs as explicit hypotheses
(`Tasks.ValuationOneMass`, `Tasks.FactorialClassGrowth`, `CoarseWeilBound`,
`AlmostAllShortPrimeIntervals theta`, `Tasks.UniformAnchorSieve`).
The checks below confirm that, beyond those hypotheses, the proofs use only the three
standard Lean axioms `propext`, `Classical.choice`, `Quot.sound` — in particular no
`sorryAx` and no project-specific `axiom`.
-/

open Lean Elab Command

/-- Fails unless `n` depends only on `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#assert_standard_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| Lean.collectAxioms n
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.toList.filter (fun a => !ok.contains a)
  if bad.isEmpty then
    logInfo m!"{n}: OK — axioms {axs.toList}"
  else
    throwError m!"{n}: non-standard axioms {bad}"

#assert_standard_axioms Erdos374.D35.ESet_densityZero
#assert_standard_axioms Erdos374.D35.ESet_count_le
#assert_standard_axioms Erdos374.D35.D3_densityZero
#assert_standard_axioms Erdos374.D35.D3_order
#assert_standard_axioms Erdos374.D35.D3_asymptotic
#assert_standard_axioms Erdos374.D35.D4_lowerDensity
#assert_standard_axioms Erdos374.D35.D4_order
#assert_standard_axioms Erdos374.D35.D5_order

#print axioms Erdos374.D35.D3_order
#print axioms Erdos374.D35.D3_asymptotic
#print axioms Erdos374.D35.D4_order
#print axioms Erdos374.D35.D5_order

#check @Erdos374.D35.D3_densityZero
#check @Erdos374.D35.D3_order
#check @Erdos374.D35.D3_asymptotic
#check @Erdos374.D35.D4_order
#check @Erdos374.D35.D5_order
