import E374.IntegrationD34

/-! Axiom audit for the closed D3 / D4 statements (no hypotheses). -/

open Lean Elab Command

elab "#assert_standard_axioms " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← liftCoreM <| Lean.collectAxioms n
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.toList.filter (fun a => !ok.contains a)
  if bad.isEmpty then
    logInfo m!"{n}: OK — axioms {axs.toList}"
  else
    throwError m!"{n}: non-standard axioms {bad}"

#assert_standard_axioms Erdos374.D35.Integration.valuationOneMass
#assert_standard_axioms Erdos374.D35.Integration.factorialGrowth
#assert_standard_axioms Erdos374.D35.Integration.coarseWeil
#assert_standard_axioms Erdos374.D35.Integration.D3_densityZero_closed
#assert_standard_axioms Erdos374.D35.Integration.D3_order_closed
#assert_standard_axioms Erdos374.D35.Integration.D3_asymptotic_closed
#assert_standard_axioms Erdos374.D35.Integration.D4_order_closed
#assert_standard_axioms Erdos374.D35.Integration.D4_lowerDensity_closed

#check @Erdos374.D35.Integration.D3_order_closed
#check @Erdos374.D35.Integration.D3_asymptotic_closed
#check @Erdos374.D35.Integration.D4_order_closed
