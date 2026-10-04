import OuterBufferedLogMaskWork

/-! Every sharp source inequality on the retained source has a uniform
positive margin. This is the exact spacing input for a future smoothed
Mellin separator; no Fourier truncation estimate is claimed here. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace OuterBufferedMaskMarginWork
open OuterBufferedLogMaskWork OuterBufferedSourceWork OuterSourceReindexWork
open OuterSeparatedLogMaskWork OuterPairSourceDecompositionWork LongerTupleEncoding

def marginCuts (δ v : ℝ) (z : Fin 9→ℝ) : Prop :=
  v+δ ≤ z 0 ∧ z 1+δ ≤ v ∧ v+δ ≤ z 2 ∧ z 3+δ ≤ v ∧ z 4+δ ≤ v ∧
    v+δ ≤ z 5 ∧ z 6+δ ≤ v ∧ v+δ ≤ z 7 ∧ z 8+δ ≤ v

theorem lt_iff_margin (δ v z : ℝ) (hδ : 0<δ) (hgap : δ≤|v-z|) :
    v<z ↔ v+δ≤z := by
  constructor
  · intro hh
    rw [abs_of_neg (sub_neg.mpr hh)] at hgap
    linarith
  · intro hh
    linarith

theorem le_iff_margin (δ v z : ℝ) (hδ : 0<δ) (hgap : δ≤|v-z|) :
    v≤z ↔ v+δ≤z := by
  constructor
  · intro hh
    rw [abs_of_nonpos (sub_nonpos.mpr hh)] at hgap
    linarith
  · intro hh
    linarith

theorem thresholdCuts_iff_margin (δ v : ℝ) (z : Fin 9→ℝ) (hδ : 0<δ)
    (hgap : ∀n,δ≤|v-z n|) : thresholdCuts v z ↔ marginCuts δ v z := by
  have hg (n : Fin 9) : δ≤|z n-v| := by simpa only [abs_sub_comm] using hgap n
  simp only [thresholdCuts,marginCuts,
    lt_iff_margin δ v (z 0) hδ (hgap 0),le_iff_margin δ (z 1) v hδ (hg 1),
    lt_iff_margin δ v (z 2) hδ (hgap 2),le_iff_margin δ (z 3) v hδ (hg 3),
    le_iff_margin δ (z 4) v hδ (hg 4),lt_iff_margin δ v (z 5) hδ (hgap 5),
    le_iff_margin δ (z 6) v hδ (hg 6),lt_iff_margin δ v (z 7) hδ (hgap 7),
    lt_iff_margin δ (z 8) v hδ (hg 8)]

theorem buffered_logMask_iff_margin (X s : ℝ) (hX : 1<X) (hs : 0<s)
    (hs1 : s≤1/1000) (hlog : 1000≤Real.log X) (r : Representation)
    (hr : r∈bufferedSource X s) (ij : ℕ×ℕ) (hij : ij∈boxPairs s) :
    logMask X s (drop r).1 (drop r).2.1 (drop r).2.2 ij.1 ij.2 r.1 ↔
      marginCuts (1/(2*X)) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) ij.1 ij.2) := by
  rw [logMask_iff_thresholdCuts X s (drop r) ij.1 ij.2 r.1 hs]
  exact thresholdCuts_iff_margin _ _ _ (by positivity)
    (buffered_log_gap X s hX hs hs1 hlog r hr ij hij)

run_cmd do
  for decl in [``lt_iff_margin, ``le_iff_margin, ``thresholdCuts_iff_margin,
      ``buffered_logMask_iff_margin] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterBufferedMaskMarginWork
