import SieveFourPrimeInner
import Mathlib.Data.List.Forall2

/-! Arbitrary-length numerical cubic prefix tests for inner and outer boxes.
Both parity modes are retained. The results concern acceptance, not the full
signed boxing comparison or a reciprocal main-term estimate. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace SieveBoxPrefix

def accepts (D : ℝ) (upper : Bool) (d : ℝ) : List ℝ → Prop
  | [] => True
  | p :: ps => (upper = false ∨ d*p^3 < D) ∧ accepts D (!upper) (d*p) ps

def stateAt : Bool → ℕ → Bool
  | upper, 0 => upper
  | upper, n+1 => stateAt (!upper) n

theorem stateAt_add_two (upper : Bool) (n : ℕ) :
    stateAt upper (n+2) = stateAt upper n := by
  simp only [stateAt, Bool.not_not]

theorem stateAt_even (upper : Bool) (k : ℕ) : stateAt upper (2*k) = upper := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, stateAt_add_two, ih]

theorem stateAt_odd (upper : Bool) (k : ℕ) : stateAt upper (2*k+1) = !upper := by
  exact stateAt_even (!upper) k

theorem accepts_iff_prefix_tests (D : ℝ) (upper : Bool) (d : ℝ) (xs : List ℝ) :
    accepts D upper d xs ↔
      ∀ n (hn : n < xs.length), stateAt upper n = true →
        d * (xs.take n).prod * xs[n]^3 < D := by
  induction xs generalizing upper d with
  | nil => simp [accepts]
  | cons a xs ih =>
    constructor
    · intro h n hn hstate
      cases n with
      | zero =>
        have hu : upper = true := hstate
        subst upper
        simpa [List.take_zero] using h.1
      | succ n =>
        have htail := (ih (!upper) (d*a)).mp h.2 n (Nat.lt_of_succ_lt_succ hn) hstate
        simpa only [List.take_succ_cons, List.prod_cons, List.getElem_cons_succ,
          mul_assoc] using htail
    · intro h
      refine ⟨?_, (ih (!upper) (d*a)).mpr ?_⟩
      · cases upper with
        | false => exact Or.inl rfl
        | true =>
          right
          have hh := h (0 : ℕ) (by simp) rfl
          simpa only [List.take_zero, List.prod_nil, mul_one, List.getElem_cons_zero] using hh
      · intro n hn hstate
        have hh := h (n+1) (by simpa using Nat.succ_lt_succ hn) hstate
        simpa only [List.take_succ_cons, List.prod_cons, List.getElem_cons_succ,
          mul_assoc] using hh

theorem accepts_natCast_iff (D : ℝ) (upper : Bool) (d : ℕ) (ps : List ℕ) :
    accepts D upper (d : ℝ) (ps.map (fun p : ℕ => (p : ℝ))) ↔
      SievePrefix.accepts (SieveRosser.cubicGate D) upper d ps := by
  induction ps generalizing upper d with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, accepts, SievePrefix.accepts, SieveRosser.cubicGate,
      Nat.cast_mul, Nat.cast_pow]
    rw [← Nat.cast_mul, ih]

/-- Simultaneously decrease each entry and the initial product. Nonnegativity
is required only on the smaller data; it then holds on the larger data too. -/
theorem accepts_mono (D : ℝ) (upper : Bool) (d e : ℝ) (xs ys : List ℝ)
    (hd : 0 ≤ d) (hde : d ≤ e)
    (hxy : List.Forall₂ (fun x y => 0 ≤ x ∧ x ≤ y) xs ys)
    (haccept : accepts D upper e ys) : accepts D upper d xs := by
  induction hxy generalizing upper d e with
  | nil => trivial
  | @cons a b xs ys hab hrest ih =>
    have hb : 0 ≤ b := hab.1.trans hab.2
    have he : 0 ≤ e := hd.trans hde
    have hmul : d*a ≤ e*b := mul_le_mul hde hab.2 hab.1 he
    have hcube : d*a^3 ≤ e*b^3 :=
      mul_le_mul hde (pow_le_pow_left₀ hab.1 hab.2 3) (pow_nonneg hab.1 3) he
    refine ⟨?_, ih (!upper) (d*a) (e*b) (mul_nonneg hd hab.1) hmul haccept.2⟩
    rcases haccept.1 with hu | hg
    · exact Or.inl hu
    · exact Or.inr (hcube.trans_lt hg)

/-- Raise every entry and the running product. The stronger inner level is
used exactly; no replacement of its exponent by one is made. -/
theorem accepts_rpow (D q : ℝ) (upper : Bool) (d : ℝ) (xs : List ℝ)
    (hD : 0 ≤ D) (hq : 0 < q) (hd : 0 ≤ d)
    (hx : ∀ x ∈ xs, 0 ≤ x) (haccept : accepts (D^(1/q)) upper d xs) :
    accepts D upper (d^q) (xs.map (fun x => x^q)) := by
  induction xs generalizing upper d with
  | nil => trivial
  | cons a xs ih =>
    have ha : 0 ≤ a := hx a (by simp)
    have htail := ih (!upper) (d*a) (mul_nonneg hd ha)
      (fun x hmem => hx x (by simp [hmem])) haccept.2
    refine ⟨?_, ?_⟩
    · rcases haccept.1 with hu | hg
      · exact Or.inl hu
      · exact Or.inr (SieveFourPrimeInner.inner_pair_power_bound D q d a hD hq hd ha hg)
    · simpa only [Real.mul_rpow hd ha] using htail

theorem inner_accepts (D q : ℝ) (upper : Bool) (xs ys : List ℝ)
    (hD : 0 ≤ D) (hq : 0 < q)
    (hxy : List.Forall₂ (fun x y => 0 ≤ x ∧ 0 ≤ y ∧ y ≤ x^q) xs ys)
    (haccept : accepts (D^(1/q)) upper 1 xs) : accepts D upper 1 ys := by
  have hx : ∀ x ∈ xs, 0 ≤ x := by
    clear haccept
    induction hxy with
    | nil => simp
    | @cons a b xs ys hab hrest ih =>
      intro x hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hab.1
      · exact ih x hmem
  have hpowered := accepts_rpow D q upper 1 xs hD hq zero_le_one hx haccept
  have hrel : List.Forall₂ (fun y z => 0 ≤ y ∧ y ≤ z) ys (xs.map (fun x => x^q)) := by
    clear haccept hx hpowered
    induction hxy with
    | nil => exact List.Forall₂.nil
    | cons hab hrest ih => exact List.Forall₂.cons hab.2 ih
  exact accepts_mono D upper 1 (1^q) ys (xs.map (fun x => x^q))
    zero_le_one (by simp) hrel hpowered

theorem outer_accepts_nat (D : ℝ) (upper : Bool) (xs : List ℝ) (ps : List ℕ)
    (hxp : List.Forall₂ (fun (x : ℝ) (p : ℕ) => 0 ≤ x ∧ x ≤ (p : ℝ)) xs ps)
    (haccept : SievePrefix.accepts (SieveRosser.cubicGate D) upper 1 ps) :
    accepts D upper 1 xs := by
  have hrel : List.Forall₂ (fun x y => 0 ≤ x ∧ x ≤ y) xs
      (ps.map (fun p : ℕ => (p : ℝ))) := by
    clear haccept
    induction hxp with
    | nil => exact List.Forall₂.nil
    | cons hab hrest ih => exact List.Forall₂.cons hab ih
  have hh := (accepts_natCast_iff D upper 1 ps).mpr haccept
  exact accepts_mono D upper 1 1 xs (ps.map (fun p : ℕ => (p : ℝ)))
    zero_le_one le_rfl hrel (by simpa only [Nat.cast_one] using hh)

theorem inner_accepts_nat (D q : ℝ) (upper : Bool) (xs : List ℝ) (ps : List ℕ)
    (hD : 0 ≤ D) (hq : 0 < q)
    (hxp : List.Forall₂ (fun (x : ℝ) (p : ℕ) => 0 ≤ x ∧ (p : ℝ) ≤ x^q) xs ps)
    (haccept : accepts (D^(1/q)) upper 1 xs) :
    SievePrefix.accepts (SieveRosser.cubicGate D) upper 1 ps := by
  have hrel : List.Forall₂ (fun x y => 0 ≤ x ∧ 0 ≤ y ∧ y ≤ x^q) xs
      (ps.map (fun p : ℕ => (p : ℝ))) := by
    clear haccept
    induction hxp with
    | nil => exact List.Forall₂.nil
    | cons hab hrest ih =>
      exact List.Forall₂.cons ⟨hab.1, Nat.cast_nonneg _, hab.2⟩ ih
  exact (accepts_natCast_iff D upper 1 ps).mp
    (by simpa only [Nat.cast_one] using
      inner_accepts D q upper xs (ps.map (fun p : ℕ => (p : ℝ))) hD hq hrel haccept)

theorem selected_inner_of_sublist (D q : ℝ) (upper : Bool)
    (xs : List ℝ) (ps ambient : List ℕ) (hD : 0 ≤ D) (hq : 0 < q)
    (hxp : List.Forall₂ (fun (x : ℝ) (p : ℕ) => 0 ≤ x ∧ (p : ℝ) ≤ x^q) xs ps)
    (haccept : accepts (D^(1/q)) upper 1 xs) (hsub : ps.Sublist ambient) :
    ps.toFinset ∈ SieveRosser.selected D upper ambient :=
  SievePrefix.selected_of_sublist_accepts (SieveRosser.cubicGate D) upper 1 ambient ps
    hsub (inner_accepts_nat D q upper xs ps hD hq hxp haccept)

theorem outer_accepts_map (D : ℝ) (upper : Bool) (f : ℕ → ℝ) (ps : List ℕ)
    (hf : ∀ p ∈ ps, 0 ≤ f p ∧ f p ≤ (p : ℝ))
    (haccept : SievePrefix.accepts (SieveRosser.cubicGate D) upper 1 ps) :
    accepts D upper 1 (ps.map f) := by
  apply outer_accepts_nat D upper (ps.map f) ps ?_ haccept
  exact List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr hf)

theorem inner_accepts_map (D q : ℝ) (upper : Bool) (f : ℕ → ℝ) (ps : List ℕ)
    (hD : 0 ≤ D) (hq : 0 < q)
    (hf : ∀ p ∈ ps, 0 ≤ f p ∧ (p : ℝ) ≤ (f p)^q)
    (haccept : accepts (D^(1/q)) upper 1 (ps.map f)) :
    SievePrefix.accepts (SieveRosser.cubicGate D) upper 1 ps := by
  apply inner_accepts_nat D q upper (ps.map f) ps hD hq ?_ haccept
  exact List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr hf)

#print axioms inner_accepts_nat
#print axioms outer_accepts_nat
run_cmd do
  for decl in [``stateAt_add_two, ``stateAt_even, ``stateAt_odd,
      ``accepts_iff_prefix_tests, ``accepts_natCast_iff, ``accepts_mono, ``accepts_rpow,
      ``inner_accepts, ``outer_accepts_nat, ``inner_accepts_nat, ``selected_inner_of_sublist,
      ``outer_accepts_map, ``inner_accepts_map] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveBoxPrefix
end


