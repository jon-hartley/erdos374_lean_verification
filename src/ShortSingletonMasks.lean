import ShortSingletonFourierL1

/-! Exact separation of an interval mask and a physical high mask.
The three integer endpoints are arbitrary; clamping is exact on q≤Q. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace ShortSingletonMasks
open ShortSingletonFourier

abbrev Frequency (Q : ℕ) := ZMod (2*Q+1)
abbrev Mode (Q : ℕ) := Frequency Q ⊕ (Frequency Q × Frequency Q)

def prefixIndicator (J q : ℕ) : ℂ := if q ≤ J then 1 else 0

def intervalPhase (Q : ℕ) (k : Frequency Q) (lo hi : ℕ) : ℂ :=
  (phase Q k (min hi Q) - phase Q k (min lo Q))/2

def scalar (Q : ℕ) : Mode Q → ℂ
  | Sum.inl k => 2*coefficient Q k
  | Sum.inr (k,j) => -(2*coefficient Q k*coefficient Q j)

def leftPhase (Q : ℕ) (a : Mode Q) (lo hi : ℕ) : ℂ :=
  match a with
  | Sum.inl k => intervalPhase Q k lo hi
  | Sum.inr (k,_) => intervalPhase Q k lo hi

def highPhase (Q : ℕ) (a : Mode Q) (cut : ℕ) : ℂ :=
  match a with
  | Sum.inl _ => 1
  | Sum.inr (_,j) => phase Q j (min cut Q)

def rightPhase (Q : ℕ) (a : Mode Q) (q : ℕ) : ℂ :=
  match a with
  | Sum.inl k => phase Q (-k) q
  | Sum.inr (k,j) => phase Q (-k) q * phase Q (-j) q

theorem prefix_expansion (Q J q : ℕ) (hq : q ≤ Q) :
    prefixIndicator J q = ∑ k : Frequency Q,
      coefficient Q k * phase Q k (min J Q) * phase Q (-k) q := by
  rw [←prefix_eq Q q (min J Q) hq (min_le_right _ _)]
  unfold prefixIndicator
  have hh : q ≤ min J Q ↔ q ≤ J := by omega
  simp only [hh]

theorem intervalPhase_norm_le (Q : ℕ) (k : Frequency Q) (lo hi : ℕ) :
    ‖intervalPhase Q k lo hi‖ ≤ 1 := by
  have hh := norm_sub_le (phase Q k (min hi Q)) (phase Q k (min lo Q))
  simp only [phase_norm] at hh
  simpa only [intervalPhase, norm_div, Complex.norm_ofNat] using
    (div_le_one (by norm_num : (0:ℝ)<2)).mpr (by linarith)

theorem leftPhase_norm_le (Q : ℕ) (a : Mode Q) (lo hi : ℕ) :
    ‖leftPhase Q a lo hi‖ ≤ 1 := by
  cases a with
  | inl k => exact intervalPhase_norm_le Q k lo hi
  | inr pair => exact intervalPhase_norm_le Q pair.1 lo hi

theorem highPhase_norm (Q : ℕ) (a : Mode Q) (cut : ℕ) :
    ‖highPhase Q a cut‖ = 1 := by
  cases a with
  | inl k => exact norm_one
  | inr pair => exact phase_norm Q pair.2 _

theorem rightPhase_norm (Q : ℕ) (a : Mode Q) (q : ℕ) :
    ‖rightPhase Q a q‖ = 1 := by
  cases a with
  | inl k => exact phase_norm Q (-k) q
  | inr pair => simp only [rightPhase, norm_mul, phase_norm, mul_one]

theorem interval_expansion (Q lo hi q : ℕ) (hq : q ≤ Q) :
    prefixIndicator hi q - prefixIndicator lo q = ∑ k : Frequency Q,
      2*coefficient Q k*intervalPhase Q k lo hi*phase Q (-k) q := by
  rw [prefix_expansion Q hi q hq, prefix_expansion Q lo q hq, ←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  unfold intervalPhase
  ring

theorem separation (Q lo hi cut q : ℕ) (hq : q ≤ Q) :
    (prefixIndicator hi q-prefixIndicator lo q)*(1-prefixIndicator cut q) =
      ∑ a : Mode Q, scalar Q a * leftPhase Q a lo hi * highPhase Q a cut *
        rightPhase Q a q := by
  rw [interval_expansion Q lo hi q hq, prefix_expansion Q cut q hq,
    Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [scalar, leftPhase, highPhase, rightPhase, mul_one]
  rw [mul_sub, mul_one, Finset.sum_mul_sum]
  rw [sub_eq_add_neg, ←Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem scalar_mass (Q : ℕ) :
    (∑ a : Mode Q, ‖scalar Q a‖) =
      2*(∑ k : Frequency Q, ‖coefficient Q k‖)*(1+∑ k : Frequency Q, ‖coefficient Q k‖) := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [scalar, norm_neg, norm_mul, Complex.norm_ofNat]
  simp_rw [←Finset.mul_sum]
  rw [←Finset.sum_mul, ←Finset.mul_sum]
  ring

theorem scalar_mass_le (Q : ℕ) (B : ℝ)
    (hB : (∑ k : Frequency Q, ‖coefficient Q k‖) ≤ B) :
    (∑ a : Mode Q, ‖scalar Q a‖) ≤ 2*B*(1+B) := by
  have hC : 0 ≤ ∑ k : Frequency Q, ‖coefficient Q k‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hBp : 0 ≤ B := hC.trans hB
  rw [scalar_mass]
  gcongr

theorem scalar_mass_le_log (Q : ℕ) :
    (∑ a : Mode Q, ‖scalar Q a‖) ≤ 2*(2+Real.log Q)*(3+Real.log Q) := by
  have hh := scalar_mass_le Q (2+Real.log Q) (coefficient_l1_le_log Q)
  convert hh using 1; ring

run_cmd do
  for decl in [``prefix_expansion, ``intervalPhase_norm_le, ``leftPhase_norm_le,
      ``highPhase_norm, ``rightPhase_norm, ``interval_expansion, ``separation, ``scalar_mass,
      ``scalar_mass_le, ``scalar_mass_le_log] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "EXACT INTERVAL-AND-PHYSICAL MASK SEPARATION PASSED"

end ShortSingletonMasks
