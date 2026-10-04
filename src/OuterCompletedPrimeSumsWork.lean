import OuterCompletedIntervalWork

/-! Exact interval-prime-sum representation for each fixed divisor, tuple,
and cofactor slice of the literal separated core. The interval endpoints
depend on that slice and the physical window, but not on the summand. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators

namespace OuterCompletedPrimeSumsWork
open LongerTupleActualProfiles PositiveSharpBoxedCount
open LongPairCloseDistinctMeanWork OuterCompletedIntervalWork
open OuterPairSourceDecompositionWork

theorem weighted_sum_eq_interval (P : Finset ℕ) (f g : ℕ→ℂ)
    (lo hi : ℕ) (c : ℂ)
    (hf : ∀p∈P, f p = if lo≤p ∧ p≤hi then c else 0) :
    (∑p∈P,f p*g p) = c*∑p∈P.filter (fun p => lo≤p ∧ p≤hi),g p := by
  rw [Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  rw [hf p hp]
  split_ifs <;> simp

theorem eventually_completed_prime_sums (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ d a b k : ℕ, ∀ L R : ℝ,
      ∃ lo hi : (ℕ×ℕ)→ℕ, ∃ c : (ℕ×ℕ)→ℂ,
        (∀ij, ‖c ij‖≤1) ∧ ∀g : ℕ→ℂ,
        (∑p∈largePrimes X,
          (if (p,d,[a,b])∈separatedSource X s ∧ completedWindow d a b k L R p then
            originalWeight X s true (p,d,[a,b]) else 0)*g p) =
        ∑ij∈boxPairs s,c ij*
          ∑p∈(largePrimes X).filter (fun p => lo ij≤p ∧ p≤hi ij),g p := by
  filter_upwards [eventually_completed_box_interval s hs hs1] with X hX
  refine ⟨hX.1,hX.2.1,?_⟩
  intro d a b k L R
  have hboxes := fun ij : ℕ×ℕ => hX.2.2 d a b ij.1 ij.2 k L R
  choose lo hi c hc he using hboxes
  refine ⟨lo,hi,c,hc,?_⟩
  intro g
  calc
    _ = ∑p∈largePrimes X, (∑ij∈boxPairs s,
        if completedBoxSource X s d a b ij.1 ij.2 k L R p then
          originalWeight X s true (p,d,[a,b]) else 0)*g p := by
      apply Finset.sum_congr rfl
      intro p _
      rw [completed_weight_eq_box_sum X s hX.1 hs hs1 hX.2.1]
    _ = ∑ij∈boxPairs s, ∑p∈largePrimes X,
        (if completedBoxSource X s d a b ij.1 ij.2 k L R p then
          originalWeight X s true (p,d,[a,b]) else 0)*g p := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ij _
      exact weighted_sum_eq_interval (largePrimes X) _ g (lo ij) (hi ij) (c ij) (he ij)

/-- An interval cap survives the literal mask at the cost of only the
fixed number of box pairs. No cap for arbitrary prime phases is assumed. -/
theorem interval_sum_bound {ι : Type*} (P : Finset ℕ) (B : Finset ι) (g : ℕ→ℂ)
    (lo hi : ι→ℕ) (c : ι→ℂ) (M : ℝ)
    (hc : ∀i∈B, ‖c i‖≤1)
    (hM : ∀l h : ℕ, ‖∑p∈P.filter (fun p => l≤p ∧ p≤h),g p‖≤M) :
    ‖∑i∈B,c i*∑p∈P.filter (fun p => lo i≤p ∧ p≤hi i),g p‖≤B.card*M := by
  calc
    _ ≤ ∑i∈B, ‖c i*∑p∈P.filter (fun p => lo i≤p ∧ p≤hi i),g p‖ :=
      norm_sum_le _ _
    _ ≤ ∑_i∈B,M := Finset.sum_le_sum (fun i hiB => by
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hc i hiB)).trans (hM _ _))
    _ = _ := by simp

theorem boxPairs_card (s : ℝ) :
    (boxPairs s).card = (SieveGeometricGrid.cutoff s+1)^2 := by
  simp [boxPairs,OuterPairFixedBoxesWork.boxIndices,pow_two]

theorem eventually_completed_prime_sum_bound (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ 1000≤Real.log X ∧
      ∀ d a b k : ℕ, ∀ L R : ℝ, ∀ g : ℕ→ℂ, ∀ M : ℝ,
      (∀lo hi : ℕ, ‖∑p∈(largePrimes X).filter (fun p => lo≤p ∧ p≤hi),g p‖≤M) →
      ‖∑p∈largePrimes X,
        (if (p,d,[a,b])∈separatedSource X s ∧ completedWindow d a b k L R p then
          originalWeight X s true (p,d,[a,b]) else 0)*g p‖ ≤
        ((SieveGeometricGrid.cutoff s+1)^2:ℕ)*M := by
  filter_upwards [eventually_completed_prime_sums s hs hs1] with X hX
  refine ⟨hX.1,hX.2.1,?_⟩
  intro d a b k L R g M hM
  obtain ⟨lo,hi,c,hc,he⟩ := hX.2.2 d a b k L R
  rw [he g,←boxPairs_card s]
  exact interval_sum_bound (largePrimes X) (boxPairs s) g lo hi c M (fun i _ => hc i) hM

run_cmd do
  for decl in [``weighted_sum_eq_interval, ``eventually_completed_prime_sums,
      ``interval_sum_bound, ``boxPairs_card, ``eventually_completed_prime_sum_bound] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterCompletedPrimeSumsWork
