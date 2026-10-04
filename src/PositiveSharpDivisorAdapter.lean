import PositiveBuchstabRepresentations
import SieveDivisorWindow
import SieveSmallWeights

/-! Exact real-cutoff and divisor/cofactor adapters for the original sifted
integer windows. The prime cutoff remains strict, including when z=p.
There is no analytic estimate or arithmetic remainder bound here. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace PositiveSharpDivisorAdapter
open Erdos374.HarmanAnalytic151
open SieveDivisorWindow

theorem rough_ceil_iff_avoids (z : ℝ) (n : ℕ) :
    Rough ⌈z⌉₊ n ↔ avoids (SieveSmallWeights.pool z) n := by
  constructor
  · intro h p hp
    have hh := (SieveSmallWeights.mem_pool z p).mp hp
    exact h p hh.1 (Nat.lt_ceil.mpr hh.2)
  · intro h p hp hpz
    exact h p ((SieveSmallWeights.mem_pool z p).mpr ⟨hp,Nat.lt_ceil.mp hpz⟩)

theorem sifted_window_eq (L R z : ℝ) :
    sifted (FiniteSieveWindow.window L R) ⌈z⌉₊ =
      siftedWindow (SieveSmallWeights.pool z) L R := by
  classical
  ext n
  simp only [sifted, siftedWindow, Finset.mem_filter, rough_ceil_iff_avoids]

theorem rough_mul_prime_iff (z p n : ℕ) (hp : p.Prime) (hz : z ≤ p) :
    Rough z (p*n) ↔ Rough z n := by
  constructor
  · intro h l hl hlz hln
    exact h l hl hlz (dvd_mul_of_dvd_right hln p)
  · intro h
    exact PositiveBuchstabRepresentations.rough_mul z p n
      (PositiveBuchstabRepresentations.rough_prime z p hp hz) h

theorem sifted_divisorSlice_eq_image (L R z : ℝ) (p : ℕ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hp : p.Prime) (hz : z ≤ (p:ℝ)) :
    sifted (divisorSlice (FiniteSieveWindow.window L R) p) ⌈z⌉₊ =
      (siftedWindow (SieveSmallWeights.pool z) (L/(p:ℝ)) (R/(p:ℝ))).image
        (fun n => p*n) := by
  classical
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast hp.pos
  have hLp : 0 ≤ L/(p:ℝ) := div_nonneg hL hp0.le
  have hLRp : L/(p:ℝ) ≤ R/(p:ℝ) := div_le_div_of_nonneg_right hLR hp0.le
  have hz' : ⌈z⌉₊ ≤ p := Nat.ceil_le.mpr hz
  ext m
  constructor
  · intro hm
    obtain ⟨hms,hrough⟩ := Finset.mem_filter.mp hm
    obtain ⟨hmw,hpm⟩ := Finset.mem_filter.mp hms
    obtain ⟨n,rfl⟩ := hpm
    have hb := (mem_window_iff L R hL hLR (p*n)).mp hmw
    simp only [Nat.cast_mul] at hb
    apply Finset.mem_image.mpr
    refine ⟨n,?_,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨(mem_window_iff _ _ hLp hLRp n).mpr ?_,?_⟩
    · constructor
      · apply (div_lt_iff₀ hp0).mpr
        simpa only [mul_comm] using hb.1
      · apply (le_div_iff₀ hp0).mpr
        simpa only [mul_comm] using hb.2
    · exact (rough_ceil_iff_avoids z n).mp ((rough_mul_prime_iff ⌈z⌉₊ p n hp hz').mp hrough)
  · intro hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    obtain ⟨hnw,havoid⟩ := Finset.mem_filter.mp hn
    have hb := (mem_window_iff _ _ hLp hLRp n).mp hnw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_,dvd_mul_right p n⟩,?_⟩
    · apply (mem_window_iff L R hL hLR (p*n)).mpr
      simp only [Nat.cast_mul]
      constructor
      · have hh := (div_lt_iff₀ hp0).mp hb.1
        simpa only [mul_comm] using hh
      · have hh := (le_div_iff₀ hp0).mp hb.2
        simpa only [mul_comm] using hh
    · exact (rough_mul_prime_iff ⌈z⌉₊ p n hp hz').mpr ((rough_ceil_iff_avoids z n).mpr havoid)

theorem mul_bijOn (L R z : ℝ) (p : ℕ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hp : p.Prime) (hz : z ≤ (p:ℝ)) :
    Set.BijOn (fun n => p*n)
      (siftedWindow (SieveSmallWeights.pool z) (L/(p:ℝ)) (R/(p:ℝ)) : Set ℕ)
      (sifted (divisorSlice (FiniteSieveWindow.window L R) p) ⌈z⌉₊ : Set ℕ) := by
  classical
  rw [sifted_divisorSlice_eq_image L R z p hL hLR hp hz]
  refine ⟨?_,?_,?_⟩
  · intro n hn
    exact Finset.mem_image.mpr ⟨n,hn,rfl⟩
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hp.pos hab
  · intro m hm
    obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hm
    exact ⟨n,hn,he⟩

theorem sifted_divisorSlice_card (L R z : ℝ) (p : ℕ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hp : p.Prime) (hz : z ≤ (p:ℝ)) :
    (sifted (divisorSlice (FiniteSieveWindow.window L R) p) ⌈z⌉₊).card =
      (siftedWindow (SieveSmallWeights.pool z) (L/(p:ℝ)) (R/(p:ℝ))).card := by
  classical
  rw [sifted_divisorSlice_eq_image L R z p hL hLR hp hz]
  exact Finset.card_image_of_injective _ (fun _ _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)

run_cmd do
  for decl in [``rough_ceil_iff_avoids, ``sifted_window_eq, ``rough_mul_prime_iff,
      ``sifted_divisorSlice_eq_image, ``mul_bijOn, ``sifted_divisorSlice_card] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "EXACT STRICT-CUTOFF DIVISOR/COFACTOR BIJECTION AND CARDINALITY"
end PositiveSharpDivisorAdapter
end
