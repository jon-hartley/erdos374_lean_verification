import LongPairCofactorSwitchWork
import FourPrimeMomentWork

/-! The four-prime local square mean on every dyadic block that is
actually reached by the literal prime-cofactor contribution. This is
uniform in separate complex unit coefficients, not in correlated masks.
No aggregation or composite-cofactor mean is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators

namespace LongPairPrimeBlockMeanWork
open LongerTupleEncoding LongPairCloseDistinctMeanWork LongPairCofactorSwitchWork
open Erdos374.HarmanGram152

def inBlock (N q : ℕ) : Prop := N < q ∧ q ≤ 2*N

def active (X s Y : ℝ) (N : Fin 4 → ℕ) : Prop :=
  ∃ x ∈ Icc X (2*X), ∃ r ∈ (separatedSource X s).filter (fun r => r.2.1=1),
    ∃ k ∈ FiniteSieveWindow.primeWindow ((x-x*(Y/X))/index r) (x/index r),
      ∃ a b : ℕ, r.2.2=[a,b] ∧ inBlock (N 0) r.1 ∧ inBlock (N 1) a ∧
        inBlock (N 2) b ∧ inBlock (N 3) k

theorem eventually_active_scales (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ ∀ Y : ℝ, 0 ≤ Y → Y ≤ X/2 →
      ∀ N : Fin 4 → ℕ, active X s Y N → ∀ i, X^(57/250 : ℝ) ≤ (N i : ℝ) := by
  filter_upwards [eventually_prime_factor_lengths s hs hs1] with X hX
  refine ⟨hX.1, ?_⟩
  intro Y hY hYX N hact
  obtain ⟨x,hx,r,hr,k,hk,a,b,ht,hp,ha,hb,hkc⟩ := hact
  obtain ⟨a',b',ht',hp',ha',hb',hk'⟩ := hX.2.2 Y hY hYX x hx r hr k hk
  have he : a'=a ∧ b'=b := by simpa using ht'.symm.trans ht
  rcases he with ⟨heA, heB⟩
  subst a'
  subst b'
  have hpN : (r.1 : ℝ) ≤ 2*(N 0 : ℝ) := by exact_mod_cast hp.2
  have haN : (a : ℝ) ≤ 2*(N 1 : ℝ) := by exact_mod_cast ha.2
  have hbN : (b : ℝ) ≤ 2*(N 2 : ℝ) := by exact_mod_cast hb.2
  have hkN : (k : ℝ) ≤ 2*(N 3 : ℝ) := by exact_mod_cast hkc.2
  intro i
  fin_cases i
  · change X^(57/250 : ℝ) ≤ (N 0 : ℝ)
    linarith
  · change X^(57/250 : ℝ) ≤ (N 1 : ℝ)
    linarith
  · change X^(57/250 : ℝ) ≤ (N 2 : ℝ)
    linarith
  · change X^(57/250 : ℝ) ≤ (N 3 : ℝ)
    linarith

theorem eventually_active_square (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ∀ᶠ X : ℝ in atTop, 1 < X ∧ ∀ Y : ℝ, 0 ≤ Y → Y ≤ X/2 →
      ∀ N : Fin 4 → ℕ, active X s Y N →
        ∀ (S : Fin 4 → Finset ℕ) (coeff : Fin 4 → ℕ → ℂ) (a T σ : ℝ),
          0 ≤ T → T ≤ X^(1124/1250 : ℝ) → 1 ≤ σ →
          (∀ i, ∀ p ∈ S i, Nat.Prime p ∧ inBlock (N i) p) →
          (∀ i, ∀ p ∈ S i, ‖coeff i p‖ ≤ 1) →
          (∫ t in Icc a (a+T),
            ‖verticalDirichlet152 (S 0) (coeff 0) σ t *
              verticalDirichlet152 (S 1) (coeff 1) σ t *
              verticalDirichlet152 (S 2) (coeff 2) σ t *
              verticalDirichlet152 (S 3) (coeff 3) σ t‖^2) ≤
                FourPrimeMomentWork.point101Constant/(Real.log X)^4 := by
  filter_upwards [eventually_active_scales s hs hs1,
    FourPrimeMomentWork.eventually_point101] with X hsc hm
  refine ⟨hsc.1, ?_⟩
  intro Y hY hYX N hact S coeff a T σ hT hTX hσ hS hw
  apply hm.2 N (hsc.2 Y hY hYX N hact) S coeff a T σ hT hTX hσ
  · intro i p hp
    have hh := hS i p hp
    exact ⟨hh.1, hh.2.1.le, hh.2.2⟩
  · exact hw

#print axioms eventually_active_square
run_cmd do
  for decl in [``eventually_active_scales, ``eventually_active_square] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL PRIME COFACTOR BLOCK GEOMETRY AND LOCAL MEAN PASSED"
end LongPairPrimeBlockMeanWork
