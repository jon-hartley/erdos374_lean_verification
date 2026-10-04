import HarmanAnalytic151Dirichlet

/-! Merge-only shim. The portable parent wrapper re-declared the original
mean-square components; importing it alongside the baseline would duplicate
names. This file instead imports the SAME named maintained baseline component.
No theorem is re-declared and no proof assumption is added. UNCOMPILED. -/
#check Erdos374.HarmanAnalytic151MeanSquare.dirichlet_mean_square_le151
