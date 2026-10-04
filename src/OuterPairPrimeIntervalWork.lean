import OuterPairSourceIntervalWork
import SmallWeightPrimeCutoffWork

/-! Every fixed-box literal outer-prime slice is one interval relative to
its ambient finite prime set. The effective small-sieve coefficient is
constant until a final cutoff, then zero. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
namespace OuterPairPrimeIntervalWork
open OuterPairSourceIntervalWork SieveWeightedCutoffs LongerTupleEncoding

def primeSlice (X s : ℝ) (P : Finset ℕ) (z : ℝ→ℝ)
    (d a b i j : ℕ) : Finset ℕ :=
  P.filter (fixedBoxSource X s P z d a b i j)

theorem primeSlice_interval (X s : ℝ) (hX : 0<X) (hs : 0<s)
    (P : Finset ℕ) (z : ℝ→ℝ) (hz : ∀ p∈P, ∀ q∈P, p≤q→z q≤z p)
    (d a b i j : ℕ) :
    ∃ lo hi : ℕ, primeSlice X s P z d a b i j =
      P.filter (fun p => lo≤p ∧ p≤hi) := by
  let F := primeSlice X s P z d a b i j
  by_cases hF : F.Nonempty
  · let lo := F.min' hF
    let hi := F.max' hF
    have hlo : lo∈F := Finset.min'_mem F hF
    have hhi : hi∈F := Finset.max'_mem F hF
    have hlow : lo≤hi := Finset.min'_le F hi hhi
    refine ⟨lo,hi,?_⟩
    ext p
    constructor
    · intro hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,
        Finset.min'_le F p hp,Finset.le_max' F p hp⟩
    · intro hp
      obtain ⟨hpP,hplo,hphi⟩ := Finset.mem_filter.mp hp
      have hconv := fixedBoxSource_convex X s hX hs P z hz d a b i j lo p hi
        hplo hphi hpP (Finset.mem_filter.mp hlo).2 (Finset.mem_filter.mp hhi).2
      exact Finset.mem_filter.mpr ⟨hpP,hconv⟩
  · refine ⟨1,0,?_⟩
    have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F = _
    rw [he]
    ext p
    simp
    omega


/-- Each fixed-box prime slice carries one constant actual small-sieve
coefficient on a (possibly empty) subinterval of P. -/
theorem primeSlice_weighted_interval (X s : ℝ) (hX : 0<X) (hs : 0<s)
    (P : Finset ℕ) (z : ℝ→ℝ) (hz : ∀ p∈P, ∀ q∈P, p≤q→z q≤z p)
    (d a b i j : ℕ) :
    ∃ lo hi : ℕ, ∃ c : ℂ, ∀ p∈P,
      (if p∈primeSlice X s P z d a b i j then
        LongerTupleActualProfiles.originalWeight X s true (p,d,[a,b]) else 0) =
      if lo≤p ∧ p≤hi then c else 0 := by
  let F := primeSlice X s P z d a b i j
  by_cases hF : F.Nonempty
  · let lo := F.min' hF
    let hi := F.max' hF
    have hlo : lo∈F := Finset.min'_mem F hF
    have hhi : hi∈F := Finset.max'_mem F hF
    have hlohi : lo≤hi := Finset.min'_le F hi hhi
    have hloPos : 0<lo := by
      have hsource := (Finset.mem_filter.mp hlo).2
      have hprod := hsource.2.2.2.2.2.2.2.2.2
      by_contra hzero
      have he : lo=0 := by omega
      rw [he] at hprod
      have hpow : 0<X^(109/200:ℝ) := Real.rpow_pos_of_pos hX _
      simp [index] at hprod
      linarith
    have hFmem (p : ℕ) (hpP : p∈P) : p∈F ↔ lo≤p ∧ p≤hi := by
      constructor
      · intro hp
        exact ⟨Finset.min'_le F p hp,Finset.le_max' F p hp⟩
      · rintro ⟨hpl,hph⟩
        apply Finset.mem_filter.mpr
        exact ⟨hpP,fixedBoxSource_convex X s hX hs P z hz d a b i j lo p hi
          hpl hph hpP (Finset.mem_filter.mp hlo).2 (Finset.mem_filter.mp hhi).2⟩
    have hlohi' : lo-1≤hi := by omega
    obtain ⟨cut,hcutLo,hcutHi,hweight⟩ :=
      SmallWeightPrimeCutoffWork.originalWeight_interval X s hX hs.le
        (lo-1) hi d hlohi' [a,b]
    refine ⟨lo,cut,LongerTupleActualProfiles.originalWeight X s true (lo,d,[a,b]),?_⟩
    intro p hpP
    by_cases hpF : p∈F
    · have hpl := (hFmem p hpP).mp hpF |>.1
      have hph := (hFmem p hpP).mp hpF |>.2
      have hpI : p∈Finset.Ioc (lo-1) hi := Finset.mem_Ioc.mpr (by omega)
      have hw := hweight p hpI
      have he : lo-1+1=lo := by omega
      simp only [he] at hw
      simp only [show p∈primeSlice X s P z d a b i j from hpF,ite_true]
      simpa only [hpl,true_and] using hw
    · have hn : ¬(lo≤p ∧ p≤cut) := by
        rintro ⟨hpl,hpc⟩
        exact hpF ((hFmem p hpP).mpr ⟨hpl,hpc.trans hcutHi⟩)
      simp only [show p∉primeSlice X s P z d a b i j from hpF,
        ite_false,hn]
  · refine ⟨1,0,0,?_⟩
    intro p hpP
    have he : F=∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    have hpF : p∉primeSlice X s P z d a b i j := by change p∉F; rw [he]; simp
    have hn : ¬(1≤p ∧ p≤0) := by omega
    simp [hpF,hn]

run_cmd do
  for decl in [``primeSlice_interval, ``primeSlice_weighted_interval] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairPrimeIntervalWork
