import SieveBoxPrefix
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! A sequence-length cutoff depending only on the fixed sieve parameter.
The actual lower cubic tests imply the bound. Zero and one entries require
no test and are covered separately. No signed boxing or main-term estimate
is assumed or concluded here. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

namespace SieveBoxLength

def cutoff (s : ℝ) : ℕ := ⌊1 / s^2⌋₊ + 1

theorem one_le_cutoff (s : ℝ) : 1 ≤ cutoff s := by
  unfold cutoff
  omega

theorem rpow_length_le_prod (D e : ℝ) (xs : List ℝ) (hD : 0 < D)
    (hx : ∀ x ∈ xs, D^e ≤ x) : D^((xs.length : ℝ)*e) ≤ xs.prod := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hx a (by simp)
    have ht := ih (fun x hm => hx x (by simp [hm]))
    have ha0 : 0 ≤ a := (Real.rpow_nonneg hD.le e).trans ha
    calc
      D^(((a::xs).length : ℝ)*e) = D^e * D^((xs.length : ℝ)*e) := by
        rw [← Real.rpow_add hD]
        congr 1
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
        ring
      _ ≤ a * xs.prod := mul_le_mul ha ht (Real.rpow_nonneg hD.le _) ha0
      _ = (a::xs).prod := rfl

/-- The zero-based tested index n is the (n+1)-entry prefix. Cubing its last
entry contributes two extra powers of the lower scale. -/
theorem cubic_prefix_lower (D s : ℝ) (xs : List ℝ) (n : ℕ)
    (hD : 0 < D) (hn : n < xs.length)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x) :
    D^(((n : ℝ)+3)*s^2) ≤ (xs.take n).prod * xs[n]^3 := by
  have hp : D^((n : ℝ)*s^2) ≤ (xs.take n).prod := by
    simpa only [List.length_take, Nat.min_eq_left (Nat.le_of_lt hn)] using
      rpow_length_le_prod D (s^2) (xs.take n) hD
        (fun x hm => hx x (List.mem_of_mem_take hm))
  have hxlast := hx xs[n] (List.getElem_mem hn)
  have hp0 : 0 ≤ (xs.take n).prod := (Real.rpow_nonneg hD.le _).trans hp
  calc
    D^(((n : ℝ)+3)*s^2) = D^((n : ℝ)*s^2) * (D^(s^2))^3 := by
      rw [show ((n : ℝ)+3)*s^2 = (n : ℝ)*s^2 + s^2*(3 : ℝ) by ring,
        Real.rpow_add hD]
      congr 1
      simpa only [Nat.cast_ofNat] using Real.rpow_mul_natCast hD.le (s^2) 3
    _ ≤ (xs.take n).prod * xs[n]^3 :=
      mul_le_mul hp (pow_le_pow_left₀ (Real.rpow_nonneg hD.le _) hxlast 3)
        (pow_nonneg (Real.rpow_nonneg hD.le _) 3) hp0

theorem tested_prefix_exponent_lt (D s : ℝ) (xs : List ℝ) (n : ℕ)
    (hD : 1 < D) (hn : n < xs.length)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (htest : (xs.take n).prod * xs[n]^3 < D) : ((n : ℝ)+3)*s^2 < 1 := by
  have hh := (cubic_prefix_lower D s xs n (by linarith) hn hx).trans_lt htest
  apply (Real.rpow_lt_rpow_left_iff hD).mp
  simpa only [Real.rpow_one] using hh

theorem lower_tested_prefix_exponent_lt (D s : ℝ) (xs : List ℝ) (r : ℕ)
    (hD : 1 < D) (hr : 2*r+1 < xs.length)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts D false 1 xs) :
    (((2*r+1 : ℕ) : ℝ)+3)*s^2 < 1 := by
  have ht := (SieveBoxPrefix.accepts_iff_prefix_tests D false 1 xs).mp ha
    (2*r+1) hr (by simp only [SieveBoxPrefix.stateAt_odd, Bool.not_false])
  exact tested_prefix_exponent_lt D s xs (2*r+1) hD hr hx (by simpa using ht)

theorem lower_even_exponent (D s : ℝ) (xs : List ℝ) (r : ℕ)
    (hD : 1 < D) (hlen : xs.length = 2*r+2)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts D false 1 xs) :
    ((xs.length : ℝ)+2)*s^2 < 1 := by
  have hh := lower_tested_prefix_exponent_lt D s xs r hD (by omega) hx ha
  convert hh using 1
  simp only [hlen, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem lower_odd_exponent (D s : ℝ) (xs : List ℝ) (r : ℕ)
    (hD : 1 < D) (hlen : xs.length = 2*r+3)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts D false 1 xs) :
    ((xs.length : ℝ)+1)*s^2 < 1 := by
  have hh := lower_tested_prefix_exponent_lt D s xs r hD (by omega) hx ha
  convert hh using 1
  simp only [hlen, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem lower_length_le_floor_of_two_le (D s : ℝ) (xs : List ℝ)
    (hD : 1 < D) (hs : 0 < s) (hlen : 2 ≤ xs.length)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts D false 1 xs) : xs.length ≤ ⌊1/s^2⌋₊ := by
  let r := xs.length / 2 - 1
  have hr : 2*r+1 < xs.length := by dsimp [r]; omega
  have hh := lower_tested_prefix_exponent_lt D s xs r hD hr hx ha
  have hnat : xs.length ≤ (2*r+1)+3 := by dsimp [r]; omega
  have hreal : (xs.length : ℝ) ≤ ((2*r+1 : ℕ) : ℝ)+3 := by exact_mod_cast hnat
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  have hmul : (xs.length : ℝ)*s^2 < 1 :=
    (mul_le_mul_of_nonneg_right hreal hs2.le).trans_lt hh
  exact Nat.le_floor ((lt_div_iff₀ hs2).mpr hmul).le

theorem lower_length_le_cutoff (D s : ℝ) (xs : List ℝ)
    (hD : 1 < D) (hs : 0 < s)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts D false 1 xs) : xs.length ≤ cutoff s := by
  by_cases hlen : 2 ≤ xs.length
  · exact (lower_length_le_floor_of_two_le D s xs hD hs hlen hx ha).trans
      (Nat.le_succ _)
  · exact (by omega : xs.length ≤ 1).trans (one_le_cutoff s)

theorem accepts_level_mono (D E : ℝ) (upper : Bool) (d : ℝ) (xs : List ℝ)
    (hDE : D ≤ E) (ha : SieveBoxPrefix.accepts D upper d xs) :
    SieveBoxPrefix.accepts E upper d xs := by
  apply (SieveBoxPrefix.accepts_iff_prefix_tests E upper d xs).mpr
  intro n hn hstate
  exact ((SieveBoxPrefix.accepts_iff_prefix_tests D upper d xs).mp ha n hn hstate).trans_le hDE

/-- Inner tests have the stronger level D^(1/q); q≥1 makes every such
tested sequence admissible for the outer level used in the cutoff. -/
theorem inner_length_le_cutoff (D s q : ℝ) (xs : List ℝ)
    (hD : 1 < D) (hs : 0 < s) (hq : 1 ≤ q)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts (D^(1/q)) false 1 xs) : xs.length ≤ cutoff s := by
  have hlevel : D^(1/q) ≤ D := Real.rpow_le_self_of_one_le hD.le
    ((div_le_one (by linarith : 0 < q)).mpr hq)
  exact lower_length_le_cutoff D s xs hD hs hx
    (accepts_level_mono (D^(1/q)) D false 1 xs hlevel ha)

theorem lower_nat_length_le_cutoff (D s : ℝ) (ps : List ℕ)
    (hD : 1 < D) (hs : 0 < s)
    (hp : ∀ p ∈ ps, D^(s^2) ≤ (p : ℝ))
    (ha : SievePrefix.accepts (SieveRosser.cubicGate D) false 1 ps) :
    ps.length ≤ cutoff s := by
  have hx : ∀ x ∈ ps.map (fun p : ℕ => (p : ℝ)), D^(s^2) ≤ x := by
    intro x hx
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
    exact hp p hp'
  simpa only [List.length_map] using lower_length_le_cutoff D s
    (ps.map (fun p : ℕ => (p : ℝ))) hD hs hx
    (by simpa only [Nat.cast_one] using
      (SieveBoxPrefix.accepts_natCast_iff D false 1 ps).mpr ha)

/-- In particular the cutoff covers every subset produced by the actual
lower selector on the large-prime list. No assumed cardinality cap is used. -/
theorem selected_card_le_cutoff (D s : ℝ) (ambient : List ℕ) (S : Finset ℕ)
    (hD : 1 < D) (hs : 0 < s)
    (hp : ∀ p ∈ ambient, D^(s^2) ≤ (p : ℝ))
    (hS : S ∈ SieveRosser.selected D false ambient) : S.card ≤ cutoff s := by
  obtain ⟨ps, hsub, he, ha⟩ := (SieveRosser.mem_selected_iff D false ambient S).mp hS
  rw [← he]
  exact (List.toFinset_card_le ps).trans
    (lower_nat_length_le_cutoff D s ps hD hs
      (fun p hm => hp p (hsub.subset hm)) ha)

#print axioms lower_length_le_cutoff
#print axioms selected_card_le_cutoff
run_cmd do
  for decl in [``one_le_cutoff, ``rpow_length_le_prod, ``cubic_prefix_lower,
      ``tested_prefix_exponent_lt, ``lower_tested_prefix_exponent_lt,
      ``lower_even_exponent, ``lower_odd_exponent, ``lower_length_le_floor_of_two_le,
      ``lower_length_le_cutoff, ``accepts_level_mono, ``inner_length_le_cutoff,
      ``lower_nat_length_le_cutoff, ``selected_card_le_cutoff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "SIEVE BOX LENGTH PASSED; standard axioms only"
end SieveBoxLength
end
