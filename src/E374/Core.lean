import Erdos374_Update152

/-!
# Integration shim for `E374.Core`

In the standalone development, `E374.Core` holds verbatim copies of the project
definitions (`HasRep`, `sf`, `q`, `falling`, `prefixCount`, `DensityZero`,
`Tasks.ValuationOneMass`, `Tasks.FactorialClassGrowth`, `Tasks.UniformAnchorSieve`,
`alpha`, `theta`, `eta`, ...). Here those copies are replaced by the project's own
verified `Erdos374_Update152`, so every downstream statement refers to the *project's*
constants and the project's closed theorems can discharge its hypotheses directly.
-/
