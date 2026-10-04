import CheckedSamplingIntervalCancellation

/-!
An explicit near-pair budget for the seed's actual Vaughan Type II bands.
This extends BilinearCorrelation152. The new namespace names this proof stage;
it does not assert the completed Mangoldt cancellation theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators ComplexConjugate

namespace TypeIICancellation
open Erdos374.ReciprocalCharacter151 Erdos374.BilinearCorrelation152
open Erdos374.BilinearCancellation152

/-- Includes the diagonal, with no exclusion hidden in the correlation sum. -/
def nearby (H k l : ℕ) : Prop := k ≤ l + H ∧ l ≤ k + H

instance (H k l : ℕ) : Decidable (nearby H k l) :=
  inferInstanceAs (Decidable (k ≤ l + H ∧ l ≤ k + H))

theorem nearby_count (t : Finset ℕ) (H k : ℕ) :
    (t.filter (nearby H k)).card ≤ 2 * H + 1 := by
  have hsubset : t.filter (nearby H k) ⊆ Finset.Icc (k - H) (k + H) := by
    intro l hl
    simp only [Finset.mem_filter, nearby] at hl
    simp only [Finset.mem_Icc]
    omega
  have hcard := Finset.card_le_card hsubset
  rw [Nat.card_Icc] at hcard
  omega

theorem band_character_norm_le (P M d k : ℕ) (u v : ℝ) :
    ‖bandCharacter P M u v d k‖ ≤ 1 := by
  unfold bandCharacter
  split_ifs <;> simp

theorem correlation_norm_le_card (s : Finset ℕ) (P M k l : ℕ) (u v : ℝ) :
    ‖∑ d ∈ s, bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖ ≤
      (s.card : ℝ) := by
  calc
    _ ≤ ∑ d ∈ s,
        ‖bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _ ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_conj]
      calc
        _ ≤ 1 * 1 := mul_le_mul (band_character_norm_le P M d k u v)
          (band_character_norm_le P M d l u v) (norm_nonneg _) (by norm_num)
        _ = _ := by norm_num
    _ = _ := by simp

/-- Count close pairs using their trivial bound; apply cancellation only
to the remaining pairs. The full coefficient energy is preserved. -/
theorem bilinear_with_nearby_budget (s t : Finset ℕ) (H P M : ℕ)
    (u v : ℝ) (a b : ℕ → ℂ) (W R : ℝ)
    (hW : 0 ≤ W) (hR : 0 ≤ R)
    (hb : ∀ k ∈ t, ‖b k‖ ≤ W)
    (hfar : ∀ k ∈ t, ∀ l ∈ t, ¬nearby H k l →
      ‖∑ d ∈ s,
        bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖ ≤ R) :
    ‖∑ d ∈ s, a d * ∑ k ∈ t, b k * bandCharacter P M u v d k‖ ^ 2 ≤
      (∑ d ∈ s, ‖a d‖ ^ 2) * W ^ 2 * (t.card : ℝ) *
        (((2 * H + 1 : ℕ) : ℝ) * (s.card : ℝ) + (t.card : ℝ) * R) := by
  classical
  have hrow : ∀ k ∈ t,
      (∑ l ∈ t, ‖b k‖ * ‖b l‖ *
        ‖∑ d ∈ s,
          bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖) ≤
      W ^ 2 * (((2 * H + 1 : ℕ) : ℝ) * (s.card : ℝ) + (t.card : ℝ) * R) := by
    intro k hk
    calc
      _ ≤ ∑ l ∈ t, W ^ 2 * (if nearby H k l then (s.card : ℝ) else R) := by
        apply Finset.sum_le_sum
        intro l hl
        have hweight : ‖b k‖ * ‖b l‖ ≤ W ^ 2 := by
          simpa only [pow_two] using mul_le_mul (hb k hk) (hb l hl) (norm_nonneg _) hW
        apply mul_le_mul hweight _ (norm_nonneg _) (sq_nonneg W)
        split_ifs with hn
        · exact correlation_norm_le_card s P M k l u v
        · exact hfar k hk l hl hn
      _ = W ^ 2 * ((t.filter (nearby H k)).card * (s.card : ℝ) +
          (t.filter (fun l => ¬nearby H k l)).card * R) := by
        rw [← Finset.mul_sum, Finset.sum_ite]
        simp
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg W)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr (nearby_count t H k)) (Nat.cast_nonneg s.card)
        · exact mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr (Finset.card_filter_le _ _)) hR
  calc
    _ ≤ (∑ d ∈ s, ‖a d‖ ^ 2) *
        ∑ k ∈ t, ∑ l ∈ t, ‖b k‖ * ‖b l‖ *
          ‖∑ d ∈ s,
            bandCharacter P M u v d k * conj (bandCharacter P M u v d l)‖ :=
      bilinear_correlation_bound s t a b (bandCharacter P M u v)
    _ ≤ (∑ d ∈ s, ‖a d‖ ^ 2) *
        ∑ _ ∈ t, W ^ 2 *
          (((2 * H + 1 : ℕ) : ℝ) * (s.card : ℝ) + (t.card : ℝ) * R) := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrow)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- A proved weighted band estimate. All analytic inputs are discharged;
its remaining premises are the explicit far-pair coefficient windows and
the elementary coefficient-size bound. Selecting H and summing all Vaughan
bands remain separate tasks. -/
theorem reciprocal_bilinear_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ D E P M H : ℕ, cutoff ≤ D → E ≤ 2 * D →
      ∀ t : Finset ℕ, (∀ k ∈ t, 0 < k) →
      ∀ u v : ℝ, u ≠ 0 → ∀ a b : ℕ → ℂ, ∀ W : ℝ, 0 ≤ W →
        (∀ k ∈ t, ‖b k‖ ≤ W) →
        (∀ k ∈ t, ∀ l ∈ t, ¬nearby H k l →
          correlationLower D P k l < correlationUpper E M k l →
          (D : ℝ) * Real.log (D : ℝ) ^ B ≤
            |u * (1 / (k : ℝ) - 1 / (l : ℝ))| ∧
          |u * (1 / (k : ℝ) - 1 / (l : ℝ))| ≤ (D : ℝ) ^ r ∧
          2 * ((r + 3 : ℕ) : ℝ) * (|v| / |u|) *
            (1 / (k : ℝ) + 1 / (l : ℝ)) ≤ (D : ℝ)) →
        ‖∑ d ∈ Finset.Ioc D E,
          a d * ∑ k ∈ t, b k * bandCharacter P M u v d k‖ ^ 2 ≤
          (∑ d ∈ Finset.Ioc D E, ‖a d‖ ^ 2) * W ^ 2 * (t.card : ℝ) *
            (((2 * H + 1 : ℕ) : ℝ) * (D : ℝ) +
              (t.card : ℝ) * (10 * (D : ℝ) / Real.log (D : ℝ) ^ A)) := by
  obtain ⟨B, cutoff, hc⟩ := IntervalCancellation.band_reciprocal_cancellation r A
  refine ⟨B, max 2 cutoff, ?_⟩
  intro D E P M H hD hE t ht u v hu a b W hW hb hfar
  have hlog : 0 ≤ Real.log (D : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hsum := bilinear_with_nearby_budget (Finset.Ioc D E) t H P M u v a b W
    (10 * (D : ℝ) / Real.log (D : ℝ) ^ A) hW (by positivity) hb
    (by
      intro k hk l hl hn
      by_cases hempty : correlationUpper E M k l ≤ correlationLower D P k l
      · rw [interval_band_correlation D E P M k l u v (ht k hk) (ht l hl),
          Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, norm_zero]
        positivity
      · obtain ⟨hlow, hhigh, hshape⟩ := hfar k hk l hl hn (lt_of_not_ge hempty)
        exact hc D E P M k l (by omega) hE (ht k hk) (ht l hl) u v hu
          hlow hhigh hshape)
  apply hsum.trans
  have hcard : ((Finset.Ioc D E).card : ℝ) ≤ D := by
    rw [Nat.card_Ioc]
    exact_mod_cast (by omega : E - D ≤ D)
  gcongr

/-- The weighted band estimate on the pure inverse-square axis. -/
theorem square_bilinear_cancellation (r A : ℕ) :
    ∃ B cutoff : ℕ, ∀ D E P M H : ℕ, cutoff ≤ D → E ≤ 2 * D →
      ∀ t : Finset ℕ, (∀ k ∈ t, 0 < k) →
      ∀ v : ℝ, ∀ a b : ℕ → ℂ, ∀ W : ℝ, 0 ≤ W →
        (∀ k ∈ t, ‖b k‖ ≤ W) →
        (∀ k ∈ t, ∀ l ∈ t, ¬nearby H k l →
          correlationLower D P k l < correlationUpper E M k l →
          (D : ℝ) ^ 2 * Real.log (D : ℝ) ^ B ≤
            |v * (1 / (k : ℝ) ^ 2 - 1 / (l : ℝ) ^ 2)| ∧
          |v * (1 / (k : ℝ) ^ 2 - 1 / (l : ℝ) ^ 2)| ≤ (D : ℝ) ^ (r + 1)) →
        ‖∑ d ∈ Finset.Ioc D E,
          a d * ∑ k ∈ t, b k * bandCharacter P M 0 v d k‖ ^ 2 ≤
          (∑ d ∈ Finset.Ioc D E, ‖a d‖ ^ 2) * W ^ 2 * (t.card : ℝ) *
            (((2 * H + 1 : ℕ) : ℝ) * (D : ℝ) +
              (t.card : ℝ) * (10 * (D : ℝ) / Real.log (D : ℝ) ^ A)) := by
  obtain ⟨B, cutoff, hc⟩ := IntervalCancellation.band_square_cancellation r A
  refine ⟨B, max 2 cutoff, ?_⟩
  intro D E P M H hD hE t ht v a b W hW hb hfar
  have hlog : 0 ≤ Real.log (D : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ D by omega))
  have hsum := bilinear_with_nearby_budget (Finset.Ioc D E) t H P M 0 v a b W
    (10 * (D : ℝ) / Real.log (D : ℝ) ^ A) hW (by positivity) hb
    (by
      intro k hk l hl hn
      by_cases hempty : correlationUpper E M k l ≤ correlationLower D P k l
      · rw [interval_band_correlation D E P M k l 0 v (ht k hk) (ht l hl),
          Finset.Ioc_eq_empty_of_le hempty, Finset.sum_empty, norm_zero]
        positivity
      · obtain ⟨hlow, hhigh⟩ := hfar k hk l hl hn (lt_of_not_ge hempty)
        exact hc D E P M k l (by omega) hE (ht k hk) (ht l hl) v hlow hhigh)
  apply hsum.trans
  have hcard : ((Finset.Ioc D E).card : ℝ) ≤ D := by
    rw [Nat.card_Ioc]
    exact_mod_cast (by omega : E - D ≤ D)
  gcongr

end TypeIICancellation

#print axioms TypeIICancellation.reciprocal_bilinear_cancellation
#print axioms TypeIICancellation.square_bilinear_cancellation
run_cmd do
  for target in [``TypeIICancellation.reciprocal_bilinear_cancellation,
      ``TypeIICancellation.square_bilinear_cancellation] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "TYPE II CANCELLATION PASSED"

run_cmd do
  for target in [``TypeIICancellation.nearby_count,
      ``TypeIICancellation.band_character_norm_le,
      ``TypeIICancellation.correlation_norm_le_card,
      ``TypeIICancellation.bilinear_with_nearby_budget,
      ``TypeIICancellation.reciprocal_bilinear_cancellation,
      ``TypeIICancellation.square_bilinear_cancellation] do
    for ax in (← Lean.collectAxioms target) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "CHECKED SAMPLING PORT: ALL EXPORTED THEOREMS GUARDED"
