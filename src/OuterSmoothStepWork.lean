import OuterBufferedMaskMarginWork

/-! A concrete continuous transition for the normalized log masks. It is
exact outside its transition band, bounded between zero and one, and has
no support on the wrong side beyond the transition width. -/
set_option autoImplicit false
set_option maxHeartbeats 9000000
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace OuterSmoothStepWork
open OuterBufferedLogMaskWork

def transition (δ x : ℝ) : ℝ := max 0 (min 1 ((x+δ)/(2*δ)))

theorem transition_bounds (δ x : ℝ) : 0≤transition δ x ∧ transition δ x≤1 := by
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_left _ _)⟩

theorem transition_continuous (δ : ℝ) : Continuous (transition δ) := by
  unfold transition
  fun_prop

theorem transition_zero (δ x : ℝ) (hδ : 0<δ) (hx : x≤-δ) : transition δ x=0 := by
  have hh : (x+δ)/(2*δ)≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  unfold transition
  exact max_eq_left ((min_le_right _ _).trans hh)

theorem transition_one (δ x : ℝ) (hδ : 0<δ) (hx : δ≤x) : transition δ x=1 := by
  have hh : 1≤(x+δ)/(2*δ) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  simp [transition,min_eq_left hh]

theorem transition_ne_zero (δ x : ℝ) (hδ : 0<δ) (hx : transition δ x≠0) : -δ<x := by
  by_contra hh
  exact hx (transition_zero δ x hδ (le_of_not_gt hh))

theorem transition_eq_indicator (δ x : ℝ) (hδ : 0<δ) (hx : δ≤|x|) :
    transition δ x = if 0<x then 1 else 0 := by
  by_cases hp : 0<x
  · rw [ite_eq_left hp]
    exact transition_one δ x hδ (by simpa only [abs_of_pos hp] using hx)
  · rw [ite_eq_right hp]
    apply transition_zero δ x hδ
    rw [abs_of_nonpos (le_of_not_gt hp)] at hx
    linarith

def signedGap (v : ℝ) (z : Fin 9→ℝ) : Fin 9→ℝ :=
  ![z 0-v,v-z 1,z 2-v,v-z 3,v-z 4,z 5-v,v-z 6,z 7-v,v-z 8]

def smoothCuts (δ v : ℝ) (z : Fin 9→ℝ) : ℝ := ∏n : Fin 9,transition δ (signedGap v z n)

def sharpCuts (v : ℝ) (z : Fin 9→ℝ) : ℝ := if thresholdCuts v z then 1 else 0

theorem signedGap_abs (v : ℝ) (z : Fin 9→ℝ) (n : Fin 9) :
    |signedGap v z n| = |v-z n| := by
  fin_cases n <;> simp [signedGap,abs_sub_comm]

theorem smoothCuts_bounds (δ v : ℝ) (z : Fin 9→ℝ) :
    0≤smoothCuts δ v z ∧ smoothCuts δ v z≤1 := by
  constructor
  · exact Finset.prod_nonneg (fun n _ => (transition_bounds δ _).1)
  · exact Finset.prod_le_one₀ (fun n _ => (transition_bounds δ _).1)
      (fun n _ => (transition_bounds δ _).2)

theorem sharpCuts_bounds (v : ℝ) (z : Fin 9→ℝ) : 0≤sharpCuts v z ∧ sharpCuts v z≤1 := by
  unfold sharpCuts
  split_ifs <;> norm_num

theorem thresholdCuts_iff_positive (δ v : ℝ) (z : Fin 9→ℝ)
    (hδ : 0<δ) (hgap : ∀n,δ≤|v-z n|) :
    thresholdCuts v z ↔ ∀n,0<signedGap v z n := by
  have hstrict (n : Fin 9) (hn : z n≤v) : z n<v := by
    have hh := hgap n
    rw [abs_of_nonneg (sub_nonneg.mpr hn)] at hh
    linarith
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
    have h1' := hstrict 1 h1
    have h3' := hstrict 3 h3
    have h4' := hstrict 4 h4
    have h6' := hstrict 6 h6
    intro n
    fin_cases n <;> simp [signedGap] <;> linarith
  · intro hh
    have h0 := hh 0; have h1 := hh 1; have h2 := hh 2
    have h3 := hh 3; have h4 := hh 4; have h5 := hh 5
    have h6 := hh 6; have h7 := hh 7; have h8 := hh 8
    simp [signedGap] at h0 h1 h2 h3 h4 h5 h6 h7 h8
    exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,
      by linarith,by linarith,by linarith,by linarith⟩

theorem smoothCuts_eq_sharp (δ v : ℝ) (z : Fin 9→ℝ)
    (hδ : 0<δ) (hgap : ∀n,δ≤|v-z n|) : smoothCuts δ v z=sharpCuts v z := by
  have hg (n : Fin 9) : δ≤|signedGap v z n| := by rw [signedGap_abs]; exact hgap n
  have hi (n : Fin 9) := transition_eq_indicator δ (signedGap v z n) hδ (hg n)
  by_cases ht : thresholdCuts v z
  · have hp := (thresholdCuts_iff_positive δ v z hδ hgap).mp ht
    simp only [sharpCuts,ht,ite_true]
    exact Finset.prod_eq_one (fun n _ => by rw [hi n,ite_eq_left (hp n)])
  · have hn : ¬∀n,0<signedGap v z n := fun hh => ht
      ((thresholdCuts_iff_positive δ v z hδ hgap).mpr hh)
    obtain ⟨n,hn⟩ := not_forall.mp hn
    simp only [sharpCuts,ht,ite_false]
    exact Finset.prod_eq_zero (Finset.mem_univ n) (by rw [hi n,ite_eq_right hn])

theorem cuts_error_abs_le (δ v : ℝ) (z : Fin 9→ℝ) :
    |sharpCuts v z-smoothCuts δ v z|≤1 := by
  have hs := sharpCuts_bounds v z
  have hm := smoothCuts_bounds δ v z
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem error_nonzero_last_gap (δ v : ℝ) (z : Fin 9→ℝ) (hδ : 0<δ)
    (herr : sharpCuts v z-smoothCuts δ v z≠0) : -δ<v-z 8 := by
  by_cases hs : sharpCuts v z=0
  · have hm : smoothCuts δ v z≠0 := by intro hh; exact herr (by simp [hs,hh])
    have hn := (Finset.prod_ne_zero_iff.mp hm) 8 (Finset.mem_univ _)
    simpa [signedGap] using transition_ne_zero δ (signedGap v z 8) hδ hn
  · have ht : thresholdCuts v z := by
      by_contra hh
      exact hs (by simp [sharpCuts,hh])
    have hh := ht.2.2.2.2.2.2.2.2
    linarith

run_cmd do
  for decl in [``transition_bounds, ``transition_continuous, ``transition_zero,
      ``transition_one, ``transition_ne_zero, ``transition_eq_indicator,
      ``signedGap_abs, ``smoothCuts_bounds, ``sharpCuts_bounds,
      ``thresholdCuts_iff_positive, ``smoothCuts_eq_sharp, ``cuts_error_abs_le,
      ``error_nonzero_last_gap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterSmoothStepWork
