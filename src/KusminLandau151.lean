import Erdos374_Update152

/- Current-object contract, definition, and recursive axiom audit. -/
#print Erdos374.KusminLandau151.e
#check Erdos374.KusminLandau151.norm_e
#check Erdos374.KusminLandau151.e_add
#check Erdos374.KusminLandau151.cot_antitone_on
#check Erdos374.KusminLandau151.sin_pi_mul_lower
#print Erdos374.KusminLandau151.q
#print Erdos374.KusminLandau151.lineWeight
#check Erdos374.KusminLandau151.q_monotone
#check Erdos374.KusminLandau151.q_bound
#check Erdos374.KusminLandau151.factor_identity
#check Erdos374.KusminLandau151.summation_by_parts
#check Erdos374.KusminLandau151.norm_lineWeight_le
#check Erdos374.KusminLandau151.norm_lineWeight_sub
#check Erdos374.KusminLandau151.lineWeight_variation_le
#check Erdos374.KusminLandau151.phase_step
#check Erdos374.KusminLandau151.kusmin_landau_succ
#check Erdos374.KusminLandau151.kusmin_landau
#check Erdos374.KusminLandau151.e_int
#check Erdos374.KusminLandau151.e_sub_int
#check Erdos374.KusminLandau151.kusmin_landau_integer
#print axioms Erdos374.KusminLandau151.e
#print axioms Erdos374.KusminLandau151.norm_e
#print axioms Erdos374.KusminLandau151.e_add
#print axioms Erdos374.KusminLandau151.cot_antitone_on
#print axioms Erdos374.KusminLandau151.sin_pi_mul_lower
#print axioms Erdos374.KusminLandau151.q
#print axioms Erdos374.KusminLandau151.lineWeight
#print axioms Erdos374.KusminLandau151.q_monotone
#print axioms Erdos374.KusminLandau151.q_bound
#print axioms Erdos374.KusminLandau151.factor_identity
#print axioms Erdos374.KusminLandau151.summation_by_parts
#print axioms Erdos374.KusminLandau151.norm_lineWeight_le
#print axioms Erdos374.KusminLandau151.norm_lineWeight_sub
#print axioms Erdos374.KusminLandau151.lineWeight_variation_le
#print axioms Erdos374.KusminLandau151.phase_step
#print axioms Erdos374.KusminLandau151.kusmin_landau_succ
#print axioms Erdos374.KusminLandau151.kusmin_landau
#print axioms Erdos374.KusminLandau151.e_int
#print axioms Erdos374.KusminLandau151.e_sub_int
#print axioms Erdos374.KusminLandau151.kusmin_landau_integer

run_cmd do
  for target in [
``Erdos374.KusminLandau151.e, ``Erdos374.KusminLandau151.norm_e, ``Erdos374.KusminLandau151.e_add, ``Erdos374.KusminLandau151.cot_antitone_on, ``Erdos374.KusminLandau151.sin_pi_mul_lower, ``Erdos374.KusminLandau151.q, ``Erdos374.KusminLandau151.lineWeight, ``Erdos374.KusminLandau151.q_monotone, ``Erdos374.KusminLandau151.q_bound, ``Erdos374.KusminLandau151.factor_identity, ``Erdos374.KusminLandau151.summation_by_parts, ``Erdos374.KusminLandau151.norm_lineWeight_le, ``Erdos374.KusminLandau151.norm_lineWeight_sub, ``Erdos374.KusminLandau151.lineWeight_variation_le, ``Erdos374.KusminLandau151.phase_step, ``Erdos374.KusminLandau151.kusmin_landau_succ, ``Erdos374.KusminLandau151.kusmin_landau, ``Erdos374.KusminLandau151.e_int, ``Erdos374.KusminLandau151.e_sub_int, ``Erdos374.KusminLandau151.kusmin_landau_integer
] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in retained Kusmin target {target}"
