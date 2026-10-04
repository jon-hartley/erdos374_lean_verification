import OuterPairPrimeIntervalWork

/-! Instantiation of the interval and constant-weight structure at the
actual large-band prime set and cube-root tuple cutoff. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter
namespace OuterPairActualIntervalWork
open SieveWeightedCutoffs PositiveSharpBoxedCount LongerTupleActualProfiles
open OuterPairPrimeIntervalWork

theorem cutoffThree_antitone (X s : ℝ) (hX : 0<X)
    (p q : ℕ) (hp : 0<p) (hpq : p≤q) :
    cutoffThree X s q≤cutoffThree X s p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  have hpqR : (p:ℝ)≤q := by exact_mod_cast hpq
  have hnum : 0≤level X s := by unfold level; exact Real.rpow_nonneg hX.le _
  have hD : level X s/q≤level X s/p :=
    div_le_div_of_nonneg_left hnum hpR hpqR
  have hD0 : 0≤level X s/q := div_nonneg hnum (by exact_mod_cast (show 0≤q by omega))
  unfold cutoffThree
  exact Real.rpow_le_rpow hD0 hD (by norm_num)

theorem eventually_actual_prime_interval (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ d a b i j : ℕ, ∃ lo hi : ℕ, ∃ c : ℂ,
        ∀ p∈largePrimes X,
          (if p∈primeSlice X s (largePrimes X) (cutoffThree X s) d a b i j then
            originalWeight X s true (p,d,[a,b]) else 0) =
          if lo≤p ∧ p≤hi then c else 0 := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1000:ℝ))] with X hX hlog
  refine ⟨hX,hlog,?_⟩
  have hgeom := large_band_geometry X s hX hs hs1 hlog
  have hz : ∀ p∈largePrimes X, ∀ q∈largePrimes X, p≤q →
      cutoffThree X s q≤cutoffThree X s p := by
    intro p hp q hq hpq
    have hp2 : 2≤p := (hgeom p hp).1
    exact cutoffThree_antitone X s (by linarith) p q (by omega) hpq
  intro d a b i j
  exact primeSlice_weighted_interval X s (by linarith) hs
    (largePrimes X) (cutoffThree X s) hz d a b i j

run_cmd do
  for decl in [``cutoffThree_antitone, ``eventually_actual_prime_interval] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterPairActualIntervalWork
