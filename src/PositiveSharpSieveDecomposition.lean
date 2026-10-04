import PositiveSharpBuchstab
import SieveCappedUpperFinite
import SieveFrozenPrimeWindow

/-! The literal five-term Buchstab specialization on a physical backward
window. The final upper sieve cutoff is floor(sqrt(2X))+1, so square roots
at the endpoint are included among the sieve primes. All arithmetic sieve
counts remain present; no estimate for their remainders is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace PositiveSharpSieveDecomposition
open Erdos374.HarmanAnalytic151 SieveWeightedScalarBudget SieveWeightedCutoffs
open SieveCappedUpperMainTerms PositiveSharpBuchstab

def lowerCutoff (X s : ℝ) : ℕ := ⌈X^alpha s⌉₊
def upperCutoff (X : ℝ) : ℕ := ⌊Real.sqrt (2*X)⌋₊+1
def sieveCutoff (X s : ℝ) (p : ℕ) : ℕ :=
  if p<firstCutoff X then ⌈cappedFourth X s p⌉₊ else innerCutoff X s p
def firstSifted (X s x y : ℝ) : ℝ :=
  ((sifted (window x y) (lowerCutoff X s)).card:ℝ)
def smallNegative (X s x y : ℝ) : ℝ :=
  ∑ p∈primeBand (lowerCutoff X s) (firstCutoff X),
    ((sifted (divisorSlice (window x y) p) ⌈cappedFourth X s p⌉₊).card:ℝ)
def largeNegative (X s x y : ℝ) : ℝ :=
  ∑ p∈primeBand (firstCutoff X) (upperCutoff X),
    ((sifted (divisorSlice (window x y) p) (innerCutoff X s p)).card:ℝ)

theorem floor_sqrt_eq (u : ℝ) (hu : 0≤u) : ⌊Real.sqrt u⌋₊=Nat.sqrt ⌊u⌋₊ := by
  apply Nat.le_antisymm
  · apply Nat.le_sqrt'.mpr
    apply (Nat.le_floor_iff hu).mpr
    have hh := (Real.le_sqrt (by positivity : (0:ℝ)≤(⌊Real.sqrt u⌋₊:ℝ)) hu).mp
      (Nat.floor_le (Real.sqrt_nonneg u))
    exact_mod_cast hh
  · apply (Nat.le_floor_iff (Real.sqrt_nonneg u)).mpr
    apply Real.le_sqrt_of_sq_le
    have hh : ((Nat.sqrt ⌊u⌋₊:ℕ):ℝ)^2≤(⌊u⌋₊:ℝ) := by
      exact_mod_cast Nat.sqrt_le' ⌊u⌋₊
    exact hh.trans (Nat.floor_le hu)

theorem upperCutoff_eq (X : ℝ) (hX : 0≤X) :
    upperCutoff X=FiniteSieveWindow.topCutoff (2*X) := by
  unfold upperCutoff FiniteSieveWindow.topCutoff
  rw [floor_sqrt_eq _ (by positivity)]

theorem lower_le_middle (X s : ℝ) (hX : 1≤X) (hs : 0≤s) :
    lowerCutoff X s≤firstCutoff X := by
  apply Nat.ceil_mono
  apply Real.rpow_le_rpow_of_exponent_le hX
  unfold alpha
  linarith

theorem middle_le_last (X : ℝ) (hX : 1≤X) : firstCutoff X≤lastCutoff X := by
  apply Nat.ceil_mono
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_le_rpow_of_exponent_le hX (by norm_num)

theorem physical_cutoff_guards (X x y : ℝ) (hX : 8≤X)
    (hx : X≤x ∧ x≤2*X) (hy : 0<y ∧ y≤X/2) :
    1≤x-y ∧ x-y≤x ∧ Nat.sqrt ⌊x⌋₊≤⌊x-y⌋₊ ∧
      lastCutoff X≤FiniteSieveWindow.topCutoff x ∧
      FiniteSieveWindow.topCutoff x≤upperCutoff X := by
  have hxp : 0≤x := by linarith [hx.1]
  have hX0 : 0≤X := by linarith
  have hroot : Real.sqrt (2*X)≤X/2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · linarith
    · nlinarith [mul_nonneg hX0 (show 0≤X-8 by linarith)]
  have hxroot := Real.sqrt_le_sqrt hx.2
  have hfloor : ⌊Real.sqrt x⌋₊≤⌊x-y⌋₊ := Nat.floor_mono (by linarith [hy.2,hx.1])
  rw [floor_sqrt_eq x hxp] at hfloor
  have hlast : lastCutoff X≤FiniteSieveWindow.topCutoff x := by
    unfold lastCutoff FiniteSieveWindow.topCutoff
    rw [← floor_sqrt_eq x hxp]
    exact (Nat.ceil_le_floor_add_one _).trans
      (Nat.add_le_add_right (Nat.floor_mono (Real.sqrt_le_sqrt hx.1)) 1)
  have hupper : FiniteSieveWindow.topCutoff x≤upperCutoff X := by
    rw [upperCutoff_eq X hX0]
    exact Nat.add_le_add_right (Nat.sqrt_le_sqrt (Nat.floor_mono hx.2)) 1
  exact ⟨by linarith [hx.1,hy.2],by linarith [hy.1],hfloor,hlast,hupper⟩

theorem sieveCutoff_small (X s : ℝ) (p : ℕ) (hp : p<firstCutoff X) :
    sieveCutoff X s p=⌈cappedFourth X s p⌉₊ := by simp only [sieveCutoff,ite_eq_left hp]

theorem sieveCutoff_large (X s : ℝ) (p : ℕ) (hp : firstCutoff X≤p) :
    sieveCutoff X s p=innerCutoff X s p := by
  simp only [sieveCutoff,ite_eq_right (not_lt.mpr hp)]

theorem sieveCutoff_le_prime (X s : ℝ) (hX : 1<X) (hs : 0≤s) (p : ℕ) :
    sieveCutoff X s p≤p := by
  by_cases hp : p<firstCutoff X
  · rw [sieveCutoff_small X s p hp]
    exact Nat.ceil_le.mpr (capped_le_prime X s p)
  · rw [sieveCutoff_large X s p (by omega)]
    apply Nat.ceil_le.mpr
    exact three_le_prime X s p hX hs (Nat.ceil_le.mp (show firstCutoff X≤p by omega))

theorem small_band_bounds (X s : ℝ) (p : ℕ)
    (hp : p∈primeBand (lowerCutoff X s) (firstCutoff X)) :
    p.Prime ∧ X^alpha s≤(p:ℝ) ∧ (p:ℝ)<X^(9/35:ℝ) := by
  obtain ⟨hb,hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hb
  exact ⟨hprime,Nat.ceil_le.mp hlo,Nat.lt_ceil.mp hhi⟩

theorem large_band_bounds (X : ℝ) (p : ℕ)
    (hp : p∈primeBand (firstCutoff X) (upperCutoff X)) :
    p.Prime ∧ X^(9/35:ℝ)≤(p:ℝ) ∧ (p:ℝ)≤Real.sqrt (2*X) := by
  obtain ⟨hb,hprime⟩ := Finset.mem_filter.mp hp
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hb
  exact ⟨hprime,Nat.ceil_le.mp hlo,
    (Nat.le_floor_iff (Real.sqrt_nonneg _)).mp (by simpa only [upperCutoff,Nat.lt_add_one_iff] using hhi)⟩

theorem prime_count_lower (X s x y : ℝ) (hX : 8≤X) (hs : 0≤s)
    (hx : X≤x ∧ x≤2*X) (hy : 0<y ∧ y≤X/2) :
    firstSifted X s x y-largeNegative X s x y-smallNegative X s x y+
      (sourceTerm X s x y:ℝ)≤((FiniteSieveWindow.primeWindow (x-y) x).card:ℝ) := by
  obtain ⟨hl,hlx,hroot,hlo,hhi⟩ := physical_cutoff_guards X x y hX hx hy
  have hmain := FiniteSieveWindow.prime_count_lower_frozen_cutoffs (x-y) x
    (lowerCutoff X s) (firstCutoff X) (lastCutoff X) (upperCutoff X)
    (sieveCutoff X s) hl hlx hroot (lower_le_middle X s (by linarith) hs)
    (middle_le_last X (by linarith)) hlo hhi
    (fun p _ => sieveCutoff_le_prime X s (by linarith) hs p)
  have hsmall : (∑ p∈primeBand (lowerCutoff X s) (firstCutoff X),
      siftedSum (divisorSlice (FiniteSieveWindow.window (x-y) x) p) (sieveCutoff X s p)
        (fun _ => (1:ℝ)))=smallNegative X s x y := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [sieveCutoff_small X s p (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).2]
    simp only [siftedSum,Finset.sum_const,nsmul_eq_mul,mul_one]
    rfl
  have hlarge : (∑ p∈primeBand (firstCutoff X) (upperCutoff X),
      siftedSum (divisorSlice (FiniteSieveWindow.window (x-y) x) p) (sieveCutoff X s p)
        (fun _ => (1:ℝ)))=largeNegative X s x y := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [sieveCutoff_large X s p (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1]
    simp only [siftedSum,Finset.sum_const,nsmul_eq_mul,mul_one]
    rfl
  have hpos : (∑ p∈primeBand (firstCutoff X) (lastCutoff X),
      ∑ q∈primeBand (sieveCutoff X s p) p,
        siftedSum (divisorSlice (FiniteSieveWindow.window (x-y) x) (p*q)) q
          (fun _ => (1:ℝ)))=(sourceTerm X s x y:ℝ) := by
    rw [sourceTerm,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [sieveCutoff_large X s p (Finset.mem_Ico.mp (Finset.mem_filter.mp hp).1).1,
      Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [siftedSum,Finset.sum_const,nsmul_eq_mul,mul_one]
    rfl
  rw [hsmall,hlarge,hpos] at hmain
  have hfirst : siftedSum (FiniteSieveWindow.window (x-y) x) (lowerCutoff X s)
      (fun _ => (1:ℝ))=firstSifted X s x y := by
    simp only [siftedSum,Finset.sum_const,nsmul_eq_mul,mul_one]
    rfl
  rw [hfirst] at hmain
  linarith

run_cmd do
  for decl in [``floor_sqrt_eq, ``upperCutoff_eq, ``lower_le_middle,
      ``middle_le_last, ``physical_cutoff_guards, ``sieveCutoff_small,
      ``sieveCutoff_large, ``sieveCutoff_le_prime, ``small_band_bounds,
      ``large_band_bounds, ``prime_count_lower] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PHYSICAL PRIME-WINDOW BUCHSTAB LOWER BOUND; ALL SIEVE COUNTS RETAINED"
end PositiveSharpSieveDecomposition
end
