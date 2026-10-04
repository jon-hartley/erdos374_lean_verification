import LongerTupleDyadic

/-! Jointly active rectangle bounds up to the full short-prime endpoint
X^(8/35), including equality. This extends the third-prime range to short
outer pairs while reusing exactly the same joint family and sum partition. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators
namespace LongerTupleShortDyadic
open FourPrimePartition LongerTupleDyadic
/-- A single jointly supported pair transfers all four analytic scale
bounds to its full dyadic rectangle. -/
theorem rectangle_bounds (X s : ℝ) (M N m q : ℕ)
    (hX : 1 ≤ X) (hs : 0 < s)
    (hfour : 4 ≤ X^(9/200:ℝ)) (htwo : 2 ≤ X^((6/25:ℝ)*s^2))
    (hprodlo : X^(109/200:ℝ) < (m:ℝ)*(q:ℝ))
    (hprodhi : (m:ℝ)*(q:ℝ) < X^(1-3*s/2))
    (hqlo : X^((49/100:ℝ)*s^2) ≤ (q:ℝ))
    (hqhi : (q:ℝ) ≤ X^(8/35:ℝ))
    (hmlo : M < m) (hmhi : m ≤ 2*M) (hnlo : N < q) (hnhi : q ≤ 2*N) :
    X^(1/2:ℝ) ≤ ((M*N:ℕ):ℝ) ∧ ((M*N:ℕ):ℝ) ≤ X^(1-s) ∧
      X^(s^2/4) ≤ (N:ℝ) ∧ (N:ℝ) ≤ X^(8/35:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hmlo' : (M:ℝ) ≤ m := by exact_mod_cast hmlo.le
  have hmhi' : (m:ℝ) ≤ 2*(M:ℝ) := by exact_mod_cast hmhi
  have hnlo' : (N:ℝ) ≤ q := by exact_mod_cast hnlo.le
  have hnhi' : (q:ℝ) ≤ 2*(N:ℝ) := by exact_mod_cast hnhi
  have hmnlo : (M:ℝ)*(N:ℝ) ≤ (m:ℝ)*(q:ℝ) :=
    mul_le_mul hmlo' hnlo' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmnhi : (m:ℝ)*(q:ℝ) ≤ 4*((M:ℝ)*(N:ℝ)) := by
    have hh := mul_le_mul hmhi' hnhi' (Nat.cast_nonneg q)
      (by positivity : 0 ≤ 2*(M:ℝ))
    nlinarith
  have hlow : 4*X^(1/2:ℝ) ≤ X^(109/200:ℝ) := by
    calc
      _ ≤ X^(9/200:ℝ)*X^(1/2:ℝ) :=
        mul_le_mul_of_nonneg_right hfour (by positivity)
      _ = _ := by rw [←Real.rpow_add hX0]; norm_num
  have hupper : X^(1-3*s/2) ≤ X^(1-s) :=
    Real.rpow_le_rpow_of_exponent_le hX (by linarith)
  have hqLower : 2*X^(s^2/4) ≤ X^((49/100:ℝ)*s^2) := by
    calc
      _ ≤ X^((6/25:ℝ)*s^2)*X^(s^2/4) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [←Real.rpow_add hX0]; congr 1; ring

  rw [Nat.cast_mul]
  exact ⟨by linarith, hmnlo.trans (hprodhi.le.trans hupper),
    by linarith, hnlo'.trans hqhi⟩

/-- All factor-range assumptions are imposed only on actual related
pairs. Arbitrary unrelated members of the marginal blocks do not enter
the proof of the analytic scale bounds. -/
theorem active_rectangle (X s : ℝ) (S T : Finset ℕ) (R : ℕ → ℕ → Prop)
    (hX : 1 ≤ X) (hs : 0 < s)
    (hfour : 4 ≤ X^(9/200:ℝ)) (htwo : 2 ≤ X^((6/25:ℝ)*s^2))
    (hR : ∀ m ∈ S, ∀ q ∈ T, R m q →
      X^(109/200:ℝ) < (m:ℝ)*(q:ℝ) ∧ (m:ℝ)*(q:ℝ) < X^(1-3*s/2) ∧
      X^((49/100:ℝ)*s^2) ≤ (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ))
    (ij : ℕ × ℕ) (hij : ij ∈ jointFamily X S T R) :
    1 ≤ scale 1 ij.1 ∧ 1 ≤ scale 1 ij.2 ∧
      X^(1/2:ℝ) ≤ ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ∧
      ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ≤ X^(1-s) ∧
      X^(s^2/4) ≤ (scale 1 ij.2:ℝ) ∧ (scale 1 ij.2:ℝ) ≤ X^(8/35:ℝ) ∧
      (∀ m ∈ block S 1 ij.1, scale 1 ij.1 < m ∧ m ≤ 2*scale 1 ij.1) ∧
      (∀ q ∈ block T 1 ij.2, scale 1 ij.2 < q ∧ q ≤ 2*scale 1 ij.2) := by
  obtain ⟨_,m,hm,q,hq,hr⟩ := (mem_jointFamily X S T R ij).mp hij
  have hm' := (mem_block S 1 ij.1 m).mp hm
  have hq' := (mem_block T 1 ij.2 q).mp hq
  obtain ⟨hp0,hp1,hq0,hq1⟩ := hR m hm'.1 q hq'.1 hr
  obtain ⟨ha,hb,hc,hd⟩ := rectangle_bounds X s (scale 1 ij.1) (scale 1 ij.2) m q
    hX hs hfour htwo hp0 hp1 hq0 hq1 hm'.2.1 hm'.2.2 hq'.2.1 hq'.2.2
  exact ⟨scale_pos 1 ij.1 le_rfl, scale_pos 1 ij.2 le_rfl,
    ha,hb,hc,hd,block_bounds S 1 ij.1,block_bounds T 1 ij.2⟩

/-- The number of retained rectangles and all their analytic scale guards
are uniform over finite supports and the actual-pair relation. -/
theorem eventually_data (s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (S T : Finset ℕ) (R : ℕ → ℕ → Prop),
        (∀ m ∈ S, ∀ q ∈ T, R m q →
          X^(109/200:ℝ) < (m:ℝ)*(q:ℝ) ∧ (m:ℝ)*(q:ℝ) < X^(1-3*s/2) ∧
          X^((49/100:ℝ)*s^2) ≤ (q:ℝ) ∧ (q:ℝ) ≤ X^(8/35:ℝ)) →
        ((jointFamily X S T R).card:ℝ) ≤ X^ε ∧
        ∀ ij ∈ jointFamily X S T R,
          1 ≤ scale 1 ij.1 ∧ 1 ≤ scale 1 ij.2 ∧
          X^(1/2:ℝ) ≤ ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ∧
          ((scale 1 ij.1*scale 1 ij.2:ℕ):ℝ) ≤ X^(1-s) ∧
          X^(s^2/4) ≤ (scale 1 ij.2:ℝ) ∧ (scale 1 ij.2:ℝ) ≤ X^(8/35:ℝ) ∧
          (∀ m ∈ block S 1 ij.1, scale 1 ij.1 < m ∧ m ≤ 2*scale 1 ij.1) ∧
          (∀ q ∈ block T 1 ij.2, scale 1 ij.2 < q ∧ q ≤ 2*scale 1 ij.2) := by
  filter_upwards [FourPrimeGlobalPartition.eventually_family_cost (2*ε) (by positivity),
    PolynomialLogEnvelope.eventually_constant_bound 4 (9/200) (by norm_num) (by norm_num),
    PolynomialLogEnvelope.eventually_constant_bound 2 ((6/25)*s^2)
      (by norm_num) (by positivity)] with X hcard hfour htwo
  refine ⟨hcard.1,?_⟩
  intro S T R hR
  refine ⟨?_,fun ij hij => active_rectangle X s S T R hcard.1 hs
    hfour.2 htwo.2 hR ij hij⟩
  have hc : ((jointFamily X S T R).card:ℝ) ≤
      ((FourPrimeGlobalPartition.k X+1:ℕ):ℝ)^2 := by
    exact_mod_cast jointFamily_card_le X S T R
  exact hc.trans (by simpa only [show 2*ε/2 = ε by ring] using hcard.2)

run_cmd do
  for decl in [``rectangle_bounds, ``active_rectangle, ``eventually_data] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "JOINTLY ACTIVE FULL SHORT-PRIME RANGE DYADIC RECTANGLES PASSED"
end LongerTupleShortDyadic
