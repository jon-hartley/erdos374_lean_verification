import OuterAmbientSizeWork
import OuterTruncatedCoreWork

/-! Geometry of the nonzero continuous source, before Fourier separation.
These restrictions must be retained when applying factor moment estimates;
they need not hold throughout an unrestricted separated Fourier mode. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace OuterSmoothSupportGeometryWork
open OuterSmoothCoreWork OuterSmoothStepWork OuterSmoothErrorSupportWork
open OuterBufferedSourceWork OuterSourceReindexWork OuterBoundaryExtensionWork
open OuterSeparatedLogMaskWork LongerTupleEncoding

def activeSource (X s : ℝ) (i j : ℕ) : Finset Representation :=
  (ambient X).filter (fun r => atomMultiplier X s i j r*
    smoothCuts (width X) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) ≠ 0)

theorem active_data (X s : ℝ) (i j : ℕ) (r : Representation)
    (hr : r ∈ activeSource X s i j) :
    r ∈ ambient X ∧ tupleMask X s (drop r).2.1 (drop r).2.2 i j ∧
      smoothCuts (width X) (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) ≠ 0 := by
  obtain ⟨hr,he⟩ := Finset.mem_filter.mp hr
  have ha := (mul_ne_zero_iff.mp he).1
  have ht : tupleMask X s (drop r).2.1 (drop r).2.2 i j := by
    by_contra hh
    exact ha (by simp [atomMultiplier,hh])
  exact ⟨hr,ht,(mul_ne_zero_iff.mp he).2⟩

theorem active_gap (X s : ℝ) (hX : 0 < X) (i j : ℕ) (r : Representation)
    (hr : r ∈ activeSource X s i j) (n : Fin 9) :
    -width X < signedGap (Real.log (r.1:ℝ)) (cutoffLogs X s (drop r) i j) n := by
  have hh := (active_data X s i j r hr).2.2
  exact transition_ne_zero _ _ (by unfold width; positivity)
    ((Finset.prod_ne_zero_iff.mp hh) n (Finset.mem_univ n))

theorem active_log_geometry (X s : ℝ) (hX : 2 ≤ X) (hs : 0 ≤ s)
    (i j : ℕ) (r : Representation) (hr : r ∈ activeSource X s i j) :
    Real.log (r.1:ℝ) < (313/1000:ℝ)*Real.log X+width X ∧
    (26/35:ℝ)*Real.log X-width X < Real.log (index r:ℝ) ∧
    Real.log (index r:ℝ) < (193/250:ℝ)*Real.log X+width X := by
  have hx : 0 < X := by linarith
  have hl : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hd := active_data X s i j r hr
  have ha := ambient_data X hX r hd.1
  have hp := ha.2.2.1
  have hd0 := ha.2.2.2.2.1
  have ha0 := ha.2.2.2.2.2.1
  have hb0 := ha.2.2.2.2.2.2
  have hab := hd.2.1
  rcases hab with ⟨_,_,_,_,_,hbL,haL,_,_⟩
  have halog : (229/1000:ℝ)*Real.log X < Real.log ((drop r).2.1:ℝ) := by
    simpa only [Real.log_rpow hx] using Real.log_lt_log (Real.rpow_pos_of_pos hx _) haL
  have hblog : (229/1000:ℝ)*Real.log X < Real.log ((drop r).2.2:ℝ) := by
    simpa only [Real.log_rpow hx] using Real.log_lt_log (Real.rpow_pos_of_pos hx _) hbL
  have hc := ha.2.1
  simp only [candidateSlices,Finset.mem_product,Finset.mem_Ioc] at hc
  have hdX : ((drop r).1:ℝ) ≤ X^(1/1000:ℝ) :=
    (by exact_mod_cast hc.1.2 : ((drop r).1:ℝ) ≤ ⌊X^(1/1000:ℝ)⌋₊).trans
      (Nat.floor_le (Real.rpow_nonneg hx.le _))
  have hdlog : Real.log ((drop r).1:ℝ) ≤ (1/1000:ℝ)*Real.log X := by
    simpa only [Real.log_rpow hx] using Real.log_le_log (by positivity) hdX
  have h0 := active_gap X s hx i j r hr 0
  have h2 := active_gap X s hx i j r hr 2
  have h8 := active_gap X s hx i j r hr 8
  simp [signedGap,cutoffLogs] at h0 h2 h8
  have he : Real.log (index r:ℝ) = Real.log (r.1:ℝ)+Real.log ((drop r).1:ℝ)+
      Real.log ((drop r).2.1:ℝ)+Real.log ((drop r).2.2:ℝ) := by
    conv_lhs => rw [← rebuild_drop r ha.1]
    exact OuterPairLogConstraintsWork.log_index _ _ _ _ hp hd0 ha0 hb0
  have hslog : 0 ≤ s*Real.log X := mul_nonneg hs hl
  rw [he]
  constructor
  · nlinarith
  constructor <;> nlinarith

run_cmd do
  for decl in [``active_data, ``active_gap, ``active_log_geometry] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSmoothSupportGeometryWork
