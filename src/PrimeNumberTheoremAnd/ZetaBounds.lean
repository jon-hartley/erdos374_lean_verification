import Erdos374_Update152

/- Pure import shim. The retained Update152 object supplies the original ZetaBounds declarations. No theorem or definition is redefined. See retained_import_unification_report.json for current object checks and provenance limitations. -/

#check Zeta0EqZeta
#check riemannZeta0
#check ZetaBnd_aux1
#check ZetaBnd_aux1b
#check ZetaUpperBnd
#check ZetaLowerBound3
#check riemannZetaLogDerivResidue

#print axioms Zeta0EqZeta
#print axioms riemannZeta0
#print axioms ZetaBnd_aux1
#print axioms ZetaBnd_aux1b
#print axioms ZetaUpperBnd
#print axioms ZetaLowerBound3
#print axioms riemannZetaLogDerivResidue

run_cmd do
  let targets := [``Zeta0EqZeta, ``riemannZeta0, ``ZetaBnd_aux1,
    ``ZetaBnd_aux1b, ``ZetaUpperBnd, ``ZetaLowerBound3,
    ``riemannZetaLogDerivResidue]
  for target in targets do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in retained zeta declaration {target}"

