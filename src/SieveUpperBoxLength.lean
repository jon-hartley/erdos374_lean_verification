import SieveBoxLength

/-! The upper-mode cubic tests bound every accepted tuple length. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace SieveUpperBoxLength

theorem upper_length_le_cutoff (D s : ℝ) (xs : List ℝ)
    (hD : 1 < D) (hs : 0 < s)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts D true 1 xs) : xs.length ≤ SieveBoxLength.cutoff s := by
  by_cases hlen : 1 ≤ xs.length
  · let r := (xs.length-1)/2
    have hr : 2*r < xs.length := by dsimp [r]; omega
    have ht := (SieveBoxPrefix.accepts_iff_prefix_tests D true 1 xs).mp ha
      (2*r) hr (by simp only [SieveBoxPrefix.stateAt_even])
    have hh := SieveBoxLength.tested_prefix_exponent_lt D s xs (2*r) hD hr hx
      (by simpa only [one_mul] using ht)
    have hnat : xs.length ≤ 2*r+3 := by dsimp [r]; omega
    have hreal : (xs.length : ℝ) ≤ ((2*r : ℕ) : ℝ)+3 := by exact_mod_cast hnat
    have hs2 : 0 < s^2 := sq_pos_of_pos hs
    have hmul : (xs.length : ℝ)*s^2 < 1 :=
      (mul_le_mul_of_nonneg_right hreal hs2.le).trans_lt hh
    exact (Nat.le_floor ((lt_div_iff₀ hs2).mpr hmul).le).trans (Nat.le_succ _)
  · have hz : xs.length = 0 := by omega
    rw [hz]
    exact Nat.zero_le _

theorem inner_length_le_cutoff (D s q : ℝ) (xs : List ℝ)
    (hD : 1 < D) (hs : 0 < s) (hq : 1 ≤ q)
    (hx : ∀ x ∈ xs, D^(s^2) ≤ x)
    (ha : SieveBoxPrefix.accepts (D^(1/q)) true 1 xs) :
    xs.length ≤ SieveBoxLength.cutoff s := by
  have hlevel : D^(1/q) ≤ D := Real.rpow_le_self_of_one_le hD.le
    ((div_le_one (by linarith : 0 < q)).mpr hq)
  exact upper_length_le_cutoff D s xs hD hs hx
    (SieveBoxLength.accepts_level_mono (D^(1/q)) D true 1 xs hlevel ha)

theorem upper_nat_length_le_cutoff (D s : ℝ) (ps : List ℕ)
    (hD : 1 < D) (hs : 0 < s)
    (hp : ∀ p ∈ ps, D^(s^2) ≤ (p : ℝ))
    (ha : SievePrefix.accepts (SieveRosser.cubicGate D) true 1 ps) :
    ps.length ≤ SieveBoxLength.cutoff s := by
  have hx : ∀ x ∈ ps.map (fun p : ℕ => (p : ℝ)), D^(s^2) ≤ x := by
    intro x hx
    obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
    exact hp p hp'
  simpa only [List.length_map] using upper_length_le_cutoff D s
    (ps.map (fun p : ℕ => (p : ℝ))) hD hs hx
    (by simpa only [Nat.cast_one] using
      (SieveBoxPrefix.accepts_natCast_iff D true 1 ps).mpr ha)

theorem selected_card_le_cutoff (D s : ℝ) (ambient : List ℕ) (S : Finset ℕ)
    (hD : 1 < D) (hs : 0 < s)
    (hp : ∀ p ∈ ambient, D^(s^2) ≤ (p : ℝ))
    (hS : S ∈ SieveRosser.selected D true ambient) :
    S.card ≤ SieveBoxLength.cutoff s := by
  obtain ⟨ps, hsub, he, ha⟩ := (SieveRosser.mem_selected_iff D true ambient S).mp hS
  rw [← he]
  exact (List.toFinset_card_le ps).trans
    (upper_nat_length_le_cutoff D s ps hD hs
      (fun p hm => hp p (hsub.subset hm)) ha)

run_cmd do
  for decl in [``upper_length_le_cutoff, ``inner_length_le_cutoff,
      ``upper_nat_length_le_cutoff, ``selected_card_le_cutoff] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL UPPER PREFIX LENGTH CUTOFF"
end SieveUpperBoxLength
end
