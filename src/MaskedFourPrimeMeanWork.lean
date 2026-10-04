import MaskedPrimeTupleMeanWork
import LongPairPrimeBlockMeanWork

/-! Local logarithmic means retaining arbitrary correlated prime-tuple masks. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace MaskedFourPrimeMeanWork
open DirichletPowerCoefficients Erdos374.HarmanAnalytic151MeanSquare

theorem eventual_prime_block_card :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ N : ℕ, W ≤ (N : ℝ) →
      ∀ s : Finset ℕ, (∀ p ∈ s, Nat.Prime p ∧ N ≤ p ∧ p ≤ 2*N) →
        (s.card : ℝ) ≤ 4*N/Real.log N := by
  obtain ⟨W,hW,hcount⟩ := PrimeReciprocalBoundsRefined.eventual_primeCounting_bound_two
  refine ⟨W,hW,?_⟩
  intro N hNW s hs
  have hN2 : (2 : ℝ) ≤ N := hW.trans hNW
  have hNp : (0 : ℝ) < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hsub : s ⊆ Nat.primesLE (2*N) := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(hs p hp).2.2, (hs p hp).1⟩
  have hcard : (s.card : ℝ) ≤ 4*N/Real.log N := by
    calc
      _ ≤ ((Nat.primesLE (2*N)).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.primeCounting (2*N) : ℝ) := by rw [Nat.primesLE_card_eq_primeCounting]
      _ ≤ 2*(2*N)/Real.log (2*N) := by
        have hh := hcount ((2*N : ℕ) : ℝ) (by
          simp only [Nat.cast_mul, Nat.cast_ofNat]
          linarith)
        rw [Nat.floor_natCast] at hh
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hh
      _ ≤ 4*N/Real.log N := by
        have hl : Real.log N ≤ Real.log (2*N) := Real.log_le_log hNp (by linarith)
        convert div_le_div_of_nonneg_left (show 0 ≤ 4*(N : ℝ) by positivity) hlog hl using 1
        ring
  exact hcard

theorem eventual_block_bound :
    ∃ W : ℝ, 2 ≤ W ∧ ∀ N : Fin 4 → ℕ, (∀ i, W ≤ (N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ))
        (w : (Fin 4 → ℕ) → ℂ) (a T σ ell : ℝ),
        0 ≤ T → 1 ≤ σ → 0 < ell → (∀ i, ell ≤ Real.log (N i)) →
        T ≤ (∏ i, 2*N i : ℕ) →
        (∀ i, ∀ p ∈ P i, Nat.Prime p ∧ N i ≤ p ∧ p ≤ 2*N i) →
        S ⊆ Fintype.piFinset P → (∀ f ∈ S, ‖w f‖ ≤ 1) →
        (∫ t in Icc a (a+T),
          ‖∑ f ∈ S, (w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
            exponentialKernel151 (Real.log (productIndex f)) t‖^2) ≤
          FourPrimeMomentWork.momentConstant/ell^4 := by
  obtain ⟨W,hW,hcount⟩ := eventual_prime_block_card
  refine ⟨W,hW,?_⟩
  intro N hNW P S w a T σ ell hT hσ hell hlog hTL hP hS hw
  have hN (i : Fin 4) : 1 ≤ N i := by
    have hh := hW.trans (hNW i)
    exact_mod_cast (show (1 : ℝ) ≤ N i by linarith)
  have hcard (i : Fin 4) : ((P i).card : ℝ) ≤ (4/ell)*N i := by
    apply (hcount (N i) (hNW i) (P i) (hP i)).trans
    calc
      _ ≤ 4*(N i : ℝ)/ell := div_le_div_of_nonneg_left (by positivity) hell (hlog i)
      _ = _ := by ring
  apply (MaskedPrimeTupleMeanWork.block_bound 4 P N S w a T σ (4/ell)
    hN hT hσ (by positivity) hTL hP hcard hS hw).trans_eq
  unfold FourPrimeMomentWork.momentConstant
  ring

theorem eventually_point101 :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ ∀ N : Fin 4 → ℕ,
      (∀ i, X^(57/250 : ℝ) ≤ (N i : ℝ)) →
      ∀ (P : Fin 4 → Finset ℕ) (S : Finset (Fin 4 → ℕ))
        (w : (Fin 4 → ℕ) → ℂ) (a T σ : ℝ),
        0 ≤ T → T ≤ X^(1124/1250 : ℝ) → 1 ≤ σ →
        (∀ i, ∀ p ∈ P i, Nat.Prime p ∧ N i ≤ p ∧ p ≤ 2*N i) →
        S ⊆ Fintype.piFinset P → (∀ f ∈ S, ‖w f‖ ≤ 1) →
        (∫ t in Icc a (a+T),
          ‖∑ f ∈ S, (w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
            exponentialKernel151 (Real.log (productIndex f)) t‖^2) ≤
          FourPrimeMomentWork.point101Constant/(Real.log X)^4 := by
  obtain ⟨W,hW,hm⟩ := eventual_block_bound
  have hlarge := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 57/250)).eventually
    (eventually_ge_atTop W)
  filter_upwards [hlarge, eventually_gt_atTop (1 : ℝ)] with X hlarge hX
  refine ⟨hX,?_⟩
  intro N hN P S w a T σ hT hTX hσ hP hS hw
  have hX0 : 0<X := by linarith
  have hlog (i : Fin 4) : (57/250 : ℝ)*Real.log X ≤ Real.log (N i) := by
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) (hN i)
    rwa [Real.log_rpow hX0] at hh
  have hTL : T ≤ (∏ i, 2*N i : ℕ) := by
    calc
      T ≤ X^(1124/1250 : ℝ) := hTX
      _ ≤ X^((57/250 : ℝ)*4) := Real.rpow_le_rpow_of_exponent_le hX.le (by norm_num)
      _ = ∏ _i : Fin 4, X^(57/250 : ℝ) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
        norm_num
      _ ≤ ∏ i : Fin 4, (2*(N i : ℝ)) := Finset.prod_le_prod₀
        (fun _ _ => Real.rpow_nonneg hX0.le _) (fun i _ => (hN i).trans (by linarith))
      _ = _ := by push_cast; rfl
  apply (hm N (fun i => hlarge.trans (hN i)) P S w a T σ
    ((57/250 : ℝ)*Real.log X) hT hσ (mul_pos (by norm_num) (Real.log_pos hX))
    hlog hTL hP hS hw).trans_eq
  unfold FourPrimeMomentWork.point101Constant
  rw [mul_pow]
  ring

/-- Exact original prime-cofactor restrictions inside a rectangular block.
The completed small divisor is one; all other source cutoffs remain. -/
def literalBlock (X s L R : ℝ) (P : Fin 4 → Finset ℕ) : Finset (Fin 4 → ℕ) :=
  (Fintype.piFinset P).filter (fun f =>
    (f 0, 1, [f 1, f 2]) ∈ LongPairCloseDistinctMeanWork.separatedSource X s ∧
    f 3 ∈ FiniteSieveWindow.primeWindow
      (L / LongerTupleEncoding.index (f 0, 1, [f 1, f 2]))
      (R / LongerTupleEncoding.index (f 0, 1, [f 1, f 2])))

/-- The coupled literal moving-window mask costs no logarithmic factor
in the local Dirichlet square mean. The physical center x is fixed during
the time integral, and the estimate is uniform in that center. -/
theorem eventually_literal_block (s : ℝ) (hs : 0<s) (hs1 : s≤1/1000) :
    ∀ᶠ X : ℝ in atTop, 1<X ∧ ∀ Y : ℝ, 0≤Y → Y≤X/2 →
      ∀ x ∈ Icc X (2*X), ∀ (N : Fin 4 → ℕ) (P : Fin 4 → Finset ℕ),
        (∀ i, ∀ p ∈ P i, Nat.Prime p ∧ LongPairPrimeBlockMeanWork.inBlock (N i) p) →
        ∀ (w : (Fin 4 → ℕ) → ℂ) (a T σ : ℝ),
          0≤T → T≤X^(1124/1250 : ℝ) → 1≤σ →
          (∀ f ∈ literalBlock X s (x-x*(Y/X)) x P, ‖w f‖≤1) →
          (∫ t in Icc a (a+T),
            ‖∑ f ∈ literalBlock X s (x-x*(Y/X)) x P,
              (w f / (((productIndex f : ℝ)^σ : ℝ) : ℂ)) *
                exponentialKernel151 (Real.log (productIndex f)) t‖^2) ≤
            FourPrimeMomentWork.point101Constant/(Real.log X)^4 := by
  filter_upwards [eventually_point101,
    LongPairPrimeBlockMeanWork.eventually_active_scales s hs hs1] with X hm hsc
  refine ⟨hm.1,?_⟩
  intro Y hY hYX x hx N P hP w a T σ hT hTX hσ hw
  by_cases hne : (literalBlock X s (x-x*(Y/X)) x P).Nonempty
  · obtain ⟨f,hf⟩ := hne
    have hf' := Finset.mem_filter.mp hf
    have hPi := Fintype.mem_piFinset.mp hf'.1
    have hact : LongPairPrimeBlockMeanWork.active X s Y N := by
      refine ⟨x,hx,(f 0,1,[f 1,f 2]),?_,f 3,hf'.2.2,f 1,f 2,rfl,?_,?_,?_,?_⟩
      · exact Finset.mem_filter.mpr ⟨hf'.2.1,rfl⟩
      · exact (hP 0 _ (hPi 0)).2
      · exact (hP 1 _ (hPi 1)).2
      · exact (hP 2 _ (hPi 2)).2
      · exact (hP 3 _ (hPi 3)).2
    apply hm.2 N (hsc.2 Y hY hYX N hact) P
      (literalBlock X s (x-x*(Y/X)) x P) w a T σ hT hTX hσ
    · intro i p hp
      exact ⟨(hP i p hp).1,(hP i p hp).2.1.le,(hP i p hp).2.2⟩
    · exact Finset.filter_subset _ _
    · exact hw
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty, norm_zero, zero_pow (by omega : 2≠0), integral_zero]
    exact div_nonneg (div_nonneg FourPrimeMomentWork.momentConstant_pos.le (by positivity))
      (by positivity)

#print axioms eventually_point101
run_cmd do
  for decl in [``eventual_prime_block_card, ``eventual_block_bound, ``eventually_point101, ``eventually_literal_block] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end MaskedFourPrimeMeanWork
