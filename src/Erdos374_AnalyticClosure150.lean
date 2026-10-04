import Erdos374_Update152

/- Pure import shim for declarations already present in retained Update152. -/
#check Erdos374.AnalyticClosure150.pntInput
#check Erdos374.AnalyticClosure150.curveInput
#check Erdos374.AnalyticClosure150.thetaInput
#check Erdos374.AnalyticClosure150.candidate_main150
#check Erdos374.AnalyticClosure150.positive_lower_density150
#check Erdos374.AnalyticClosure150.candidate_main_from_original_sampling150
#print axioms Erdos374.AnalyticClosure150.pntInput
#print axioms Erdos374.AnalyticClosure150.curveInput
#print axioms Erdos374.AnalyticClosure150.thetaInput
#print axioms Erdos374.AnalyticClosure150.candidate_main150
#print axioms Erdos374.AnalyticClosure150.positive_lower_density150
#print axioms Erdos374.AnalyticClosure150.candidate_main_from_original_sampling150

run_cmd do
  for target in [
``Erdos374.AnalyticClosure150.pntInput, ``Erdos374.AnalyticClosure150.curveInput, ``Erdos374.AnalyticClosure150.thetaInput, ``Erdos374.AnalyticClosure150.candidate_main150, ``Erdos374.AnalyticClosure150.positive_lower_density150, ``Erdos374.AnalyticClosure150.candidate_main_from_original_sampling150
] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in unified retained closure target {target}"
