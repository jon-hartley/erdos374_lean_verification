import FactoredDivisorMeanSquare
import CofactorDoublingCoverage
import FactoredFrequencyParameters

/-!
A length region for the actual signed divisor remainder, with window
exponent 1/10 + ε for each fixed 0 < ε < 1/100. The .101 specialization
is below 81/800 and 21/200; the full allowed range need not be.
-/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set

namespace FactoredDivisorHarmanRegion
open MellinCofactorCoverage FactoredDivisorWeights

def windowExponent (ε : ℝ) : ℝ := 1 / 10 + ε
def tailExponent (ε : ℝ) : ℝ := 9 / 10 - ε / 2
def selectionExponent (ε : ℝ) : ℝ := ε / 4
def capExponent (ε : ℝ) : ℝ := ε / 4

theorem numeric_exponents (ε : ℝ) :
    selectionExponent ε / 10 + tailExponent ε * (10 / 9) =
      1 - 191 * ε / 360 ∧
    selectionExponent ε + tailExponent ε * (6 / 7) =
      27 / 35 - 5 * ε / 28 ∧
    1 - windowExponent ε + capExponent ε = 9 / 10 - 3 * ε / 4 := by
  dsimp [windowExponent, tailExponent, selectionExponent, capExponent]
  constructor <;> [ring; constructor <;> ring]

def eta (ell : ℝ) : ℝ := min (ell / 8) (1 / 20)

theorem eta_properties (ell ε : ℝ) (hell : 0 < ell)
    (hε : ε < 1 / 100) :
    0 < eta ell ∧ eta ell ≤ ell ∧ eta ell < 1 ∧
      eta ell ≤ ell / 4 ∧ eta ell < tailExponent ε := by
  unfold eta tailExponent
  have hpos : 0 < ell / 8 := by positivity
  have hminpos : 0 < min (ell / 8) (1 / 20 : ℝ) :=
    lt_min hpos (by norm_num)
  have hminell : min (ell / 8) (1 / 20 : ℝ) ≤ ell / 8 :=
    min_le_left _ _
  have hmin20 : min (ell / 8) (1 / 20 : ℝ) ≤ 1 / 20 :=
    min_le_right _ _
  constructor
  · exact hminpos
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem eventual_frequency_arithmetic (ε : ℝ)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      32 ≤ X ^ (ε / 16) ∧
      2 ≤ X ^ (1 - windowExponent ε) := by
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound
      32 (ε / 16) (by norm_num) (by positivity),
    PolynomialLogEnvelope.eventually_constant_bound
      2 (1 - windowExponent ε) (by norm_num)
        (by dsimp [windowExponent]; linarith)]
      with X h32 htwo
  exact ⟨h32.1, h32.2, htwo.2⟩

theorem pair_total_guards (X A ε : ℝ) (lo M N : ℕ)
    (hX : 1 ≤ X) (hA : A = ((M * N : ℕ) : ℝ))
    (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hlo : X / (32 * A) ≤ (lo : ℝ))
    (hε : 0 < ε) (h32 : 32 ≤ X ^ (ε / 16))
    (hbranch : (N : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
      X ^ (27 / 35 : ℝ) ≤ A) :
    X ^ (selectionExponent ε / 10) *
      (X ^ tailExponent ε) ^ (10 / 9 : ℝ) ≤
        (lo * M * N : ℕ) ∧
      X ^ (selectionExponent ε) *
        (X ^ tailExponent ε) ^ (6 / 7 : ℝ) ≤
        max (lo * M : ℕ) (M * N : ℕ) := by
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by
    rw [hA, Nat.cast_mul]
    positivity
  have hlo_nonneg : (0 : ℝ) ≤ lo := Nat.cast_nonneg _
  have hMr : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hloA : X ≤ 32 * (lo : ℝ) * A := by
    have hh := (div_le_iff₀ (by positivity : 0 < 32 * A)).mp hlo
    nlinarith
  have htotalPower : X ^ (1 - ε / 16) ≤ (lo : ℝ) * A := by
    have hh : 32 * X ^ (1 - ε / 16) ≤ X := by
      calc
        _ ≤ X ^ (ε / 16) * X ^ (1 - ε / 16) :=
          mul_le_mul_of_nonneg_right h32 (by positivity)
        _ = X := by
          rw [← Real.rpow_add hXp]
          convert Real.rpow_one X using 1
          ring
    nlinarith
  have hpairPower : X ^ (27 / 35 - ε / 16) ≤
      max (lo * M : ℕ) (M * N : ℕ) := by
    have hmargin : 32 * X ^ (27 / 35 - ε / 16) ≤
        X ^ (27 / 35 : ℝ) := by
      calc
        _ ≤ X ^ (ε / 16) * X ^ (27 / 35 - ε / 16) :=
          mul_le_mul_of_nonneg_right h32 (by positivity)
        _ = X ^ (27 / 35 : ℝ) := by
          rw [← Real.rpow_add hXp]
          congr 1
          ring
    have hbase : X ^ (27 / 35 - ε / 16) ≤
        max ((lo * M : ℕ) : ℝ) ((M * N : ℕ) : ℝ) := by
      rcases hbranch with hsmall | hlarge
      · have hBpos : 0 < X ^ (8 / 35 : ℝ) := by positivity
        have hproduct : X = X ^ (27 / 35 : ℝ) *
            X ^ (8 / 35 : ℝ) := by
          rw [← Real.rpow_add hXp]
          norm_num
        have hMN : A = (M : ℝ) * N := by
          simpa only [Nat.cast_mul] using hA
        have hsmallprod : (lo : ℝ) * A ≤
            ((lo * M : ℕ) : ℝ) * X ^ (8 / 35 : ℝ) := by
          rw [hMN, Nat.cast_mul]
          have hh := mul_le_mul_of_nonneg_left hsmall
            (mul_nonneg hlo_nonneg hMr)
          nlinarith
        have hcompare : X ^ (27 / 35 : ℝ) ≤
            32 * ((lo * M : ℕ) : ℝ) := by
          by_contra hnot
          have hgt : 32 * ((lo * M : ℕ) : ℝ) <
              X ^ (27 / 35 : ℝ) := lt_of_not_ge hnot
          have hmul := mul_lt_mul_of_pos_right hgt hBpos
          nlinarith [hloA, hsmallprod, hproduct]
        have hleft : X ^ (27 / 35 - ε / 16) ≤
            ((lo * M : ℕ) : ℝ) := by nlinarith [hmargin]
        exact hleft.trans (by exact_mod_cast (le_max_left (lo * M) (M * N)))
      · have hright : X ^ (27 / 35 - ε / 16) ≤
            ((M * N : ℕ) : ℝ) := by
          rw [hA] at hlarge
          exact (Real.rpow_le_rpow_of_exponent_le hX
            (by linarith : (27 / 35 - ε / 16 : ℝ) ≤ 27 / 35)).trans hlarge
        exact hright.trans (by exact_mod_cast (le_max_right (lo * M) (M * N)))
    simpa only [Nat.cast_max] using hbase
  constructor
  · have hexp : selectionExponent ε / 10 +
        tailExponent ε * (10 / 9 : ℝ) ≤ 1 - ε / 16 := by
      dsimp [selectionExponent, tailExponent]
      linarith
    have hbound := Real.rpow_le_rpow_of_exponent_le hX hexp
    have hcast : ((lo * M * N : ℕ) : ℝ) = (lo : ℝ) * A := by
      rw [hA]
      push_cast
      ring
    calc
      _ = X ^ (selectionExponent ε / 10 +
          tailExponent ε * (10 / 9 : ℝ)) := by
            rw [Real.rpow_add hXp, Real.rpow_mul hXp.le]
      _ ≤ X ^ (1 - ε / 16) := hbound
      _ ≤ (lo * M * N : ℕ) := by simpa only [hcast] using htotalPower
  · have hexp : selectionExponent ε +
        tailExponent ε * (6 / 7 : ℝ) ≤ 27 / 35 - ε / 16 := by
      dsimp [selectionExponent, tailExponent]
      linarith
    have hbound := Real.rpow_le_rpow_of_exponent_le hX hexp
    calc
      _ = X ^ (selectionExponent ε +
          tailExponent ε * (6 / 7 : ℝ)) := by
            rw [Real.rpow_add hXp, Real.rpow_mul hXp.le]
      _ ≤ X ^ (27 / 35 - ε / 16) := hbound
      _ ≤ _ := hpairPower

theorem eventually_region (α ell slack nu ε : ℝ)
    (hα : 0 < α) (hell : 0 < ell)
    (hslack : 0 < slack) (hnu : 0 < nu)
    (hε : 0 < ε) (hεsmall : ε < 1 / 100) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ),
          let A : ℝ := (M * N : ℕ)
          let Y : ℝ := X ^ windowExponent ε
          1 ≤ M → 1 ≤ N →
          X ^ α ≤ A → A ≤ X ^ (1 - ell - slack) →
          X ^ nu ≤ (N : ℝ) →
          ((N : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
            X ^ (27 / 35 : ℝ) ≤ A) →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∀ n ∈ sm, |am n| ≤ 1) →
          (∀ n ∈ sn, |an n| ≤ 1) →
          (1 / X) * (∫ x in Icc X (2 * X),
            HarmanDivisorWindow.remainder
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an)
              (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨hηpos, hηell, hηone, hηfour, hηtop⟩ :=
    eta_properties ell ε hell hεsmall
  obtain ⟨c, hc, hgeneric⟩ :=
    FactoredDivisorMeanSquare.eventually_bound
      (windowExponent ε) ell nu (selectionExponent ε)
      (eta ell) (eta ell) (capExponent ε) 9
      (by dsimp [windowExponent]; linarith) hell hnu
      (by dsimp [selectionExponent]; positivity)
      hηpos hηell hηone hηpos le_rfl
      (by dsimp [capExponent]; positivity)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hgeneric,
    CofactorDoublingCoverage.eventual_scales α ell slack hα hell hslack,
    eventual_frequency_arithmetic ε hε hεsmall,
    PolynomialLogEnvelope.eventually_constant_bound
      32 slack (by norm_num) hslack,
    PolynomialLogEnvelope.eventually_constant_bound
      2 (tailExponent ε - eta ell) (by norm_num) (by linarith),
    eventually_ge_atTop (Real.exp 1)] with X hg hcoverage hfreq
      hslackX htopX hXexp
  refine ⟨hXexp, ?_⟩
  intro M N sm sn am an
  dsimp only
  intro hM hN hAlow hAupper hNlow hbranch hsm hsn ham han
  let A : ℝ := ((M * N : ℕ) : ℝ)
  let lo := lowerCutoff X A
  let hi := upperCutoff X A
  let H : ℝ := X ^ eta ell
  let U : ℝ := X ^ tailExponent ε
  let Y : ℝ := X ^ windowExponent ε
  have hX : 1 ≤ X := hfreq.1
  have hXp : 0 < X := by linarith
  have hAp : 0 < A := by
    dsimp [A]
    exact_mod_cast Nat.mul_pos (by omega : 0 < M) (by omega : 0 < N)
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact_mod_cast Nat.mul_le_mul hM hN
  have hAX : A ≤ X := by
    have hexp : 1 - ell - slack ≤ (1 : ℝ) := by linarith
    exact hAupper.trans (by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hX hexp)
  obtain ⟨hlo, _hloone, hhi, hcap⟩ :=
    hcoverage.2 A hAlow hAupper
  have hscale : 32 * A ≤ X := by
    have h32A : 32 * A ≤
        X ^ slack * X ^ (1 - ell - slack) := by
      exact mul_le_mul hslackX.2 hAupper
        (by positivity : 0 ≤ A)
        (Real.rpow_nonneg hXp.le _)
    have hfull : X ^ ell * (32 * A) ≤ X := by
      calc
        _ ≤ X ^ ell * (X ^ slack * X ^ (1 - ell - slack)) :=
          mul_le_mul_of_nonneg_left h32A (by positivity)
        _ = X := by
          rw [← Real.rpow_add hXp, ← Real.rpow_add hXp]
          convert Real.rpow_one X using 1
          ring
    have hpowone : 1 ≤ X ^ ell := Real.one_le_rpow hX hell.le
    nlinarith [hfull]
  have hloScale : X / (32 * A) ≤ (lo : ℝ) :=
    lowerCutoff_scale X A hAp hscale
  obtain ⟨hproduct, hpair⟩ := pair_total_guards X A ε lo M N
    hX rfl hM hN hloScale hε hfreq.2.1 hbranch
  have hHroot : H ≤ (lo : ℝ) ^ (1 / 4 : ℝ) := by
    have hpow : X ^ (eta ell) ≤ X ^ (ell / 4) :=
      Real.rpow_le_rpow_of_exponent_le hX hηfour
    have hroot := Real.rpow_le_rpow
      (by positivity : 0 ≤ X ^ ell) hlo
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul hXp.le] at hroot
    have hroot' : X ^ (ell / 4) ≤
        (lo : ℝ) ^ (1 / 4 : ℝ) := by
      convert hroot using 1
      ring
    exact hpow.trans hroot'
  have hUlow : 2 * H ≤ U := by
    have hh := mul_le_mul_of_nonneg_right htopX.2
      (by positivity : 0 ≤ X ^ eta ell)
    dsimp [H, U]
    calc
      _ ≤ X ^ (tailExponent ε - eta ell) * X ^ eta ell := hh
      _ = X ^ tailExponent ε := by
        rw [← Real.rpow_add hXp]
        congr 1
        ring
  have hUX : U ≤ X := by
    dsimp [U]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hX
      (by dsimp [tailExponent]; linarith : tailExponent ε ≤ 1))
  have hUhigh : X ^ (1 - windowExponent ε + capExponent ε) ≤ U := by
    dsimp [U]
    exact Real.rpow_le_rpow_of_exponent_le hX
      (by dsimp [windowExponent, capExponent, tailExponent]; linarith)
  have hYhalf : Y ≤ X / 2 := by
    have hh : 2 * Y ≤ X := by
      dsimp [Y]
      calc
        _ ≤ X ^ (1 - windowExponent ε) * X ^ windowExponent ε :=
          mul_le_mul_of_nonneg_right hfreq.2.2 (by positivity)
        _ = X := by
          rw [← Real.rpow_add hXp]
          convert Real.rpow_one X using 1
          ring
    linarith
  have hcall := hg.2 M N sm sn am an Y H U
  dsimp only at hcall
  apply hcall hM hN hAX hlo hhi hcap hNlow hproduct hpair
  · exact le_rfl
  · exact hHroot
  · nlinarith [hUlow, (show 0 ≤ H by positivity)]
  · exact hUlow
  · exact hUX
  · exact hUhigh
  · exact le_rfl
  · exact hYhalf
  · exact hsm
  · exact hsn
  · exact ham
  · exact han

theorem eventual_numeric_witness :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      let M := FactoredFrequencyParameters.middleFactor X
      let N := FactoredFrequencyParameters.shortFactor X
      let A := FactoredFrequencyParameters.divisorScale X
      1 ≤ M ∧ 1 ≤ N ∧
        X ^ (4998 / 10000 : ℝ) ≤ A ∧
        A ≤ X ^ (1 - (4999 / 10000 : ℝ) - (1 / 10000 : ℝ)) ∧
        X ^ (1999 / 10000 : ℝ) ≤ (N : ℝ) ∧
        (N : ℝ) ≤ X ^ (8 / 35 : ℝ) := by
  filter_upwards [FactoredFrequencyParameters.eventually_factored_scales]
    with X hh
  rcases hh with ⟨hX, _hA32, hAlow, hAupper, hMlow, hNlow,
    _hK, _hKone, _hhi, _hKupper⟩
  have hMp : 1 ≤ FactoredFrequencyParameters.middleFactor X := by
    have hh : (1 : ℝ) ≤ FactoredFrequencyParameters.middleFactor X :=
      (Real.one_le_rpow hX (by norm_num)).trans hMlow
    exact_mod_cast hh
  have hNp : 1 ≤ FactoredFrequencyParameters.shortFactor X := by
    have hh : (1 : ℝ) ≤ FactoredFrequencyParameters.shortFactor X :=
      (Real.one_le_rpow hX (by norm_num)).trans hNlow
    exact_mod_cast hh
  have hAupper' :
      FactoredFrequencyParameters.divisorScale X ≤
        X ^ (1 - (4999 / 10000 : ℝ) - (1 / 10000 : ℝ)) := by
    convert hAupper using 1
    norm_num
  have hNupper : (FactoredFrequencyParameters.shortFactor X : ℝ) ≤
      X ^ (8 / 35 : ℝ) := by
    have hfloor : (FactoredFrequencyParameters.shortFactor X : ℝ) ≤
        X ^ (1 / 5 : ℝ) := Nat.floor_le (by positivity)
    exact hfloor.trans
      (Real.rpow_le_rpow_of_exponent_le hX
        (by norm_num : (1 / 5 : ℝ) ≤ 8 / 35))
  refine ⟨hX, ?_⟩
  dsimp only
  exact ⟨hMp, hNp, hAlow, hAupper', hNlow, hNupper⟩

theorem eventually_point101 (α ell slack nu : ℝ)
    (hα : 0 < α) (hell : 0 < ell)
    (hslack : 0 < slack) (hnu : 0 < nu) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, Real.exp 1 ≤ X ∧
        ∀ (M N : ℕ) (sm sn : Finset ℕ) (am an : ℕ → ℝ),
          let A : ℝ := (M * N : ℕ)
          let Y : ℝ := X ^ (101 / 1000 : ℝ)
          1 ≤ M → 1 ≤ N →
          X ^ α ≤ A → A ≤ X ^ (1 - ell - slack) →
          X ^ nu ≤ (N : ℝ) →
          ((N : ℝ) ≤ X ^ (8 / 35 : ℝ) ∨
            X ^ (27 / 35 : ℝ) ≤ A) →
          (∀ n ∈ sm, M < n ∧ n ≤ 2 * M) →
          (∀ n ∈ sn, N < n ∧ n ≤ 2 * N) →
          (∀ n ∈ sm, |am n| ≤ 1) →
          (∀ n ∈ sn, |an n| ≤ 1) →
          (1 / X) * (∫ x in Icc X (2 * X),
            HarmanDivisorWindow.remainder
              (FactoredDivisorWeights.support sm sn)
              (FactoredDivisorWeights.coefficient sm sn am an)
              (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-c) := by
  obtain ⟨c, hc, hh⟩ := eventually_region α ell slack nu (1 / 1000)
    hα hell hslack hnu (by norm_num) (by norm_num)
  refine ⟨c, hc, ?_⟩
  simpa only [windowExponent,
    show (1 / 10 : ℝ) + 1 / 1000 = 101 / 1000 by norm_num] using hh

end FactoredDivisorHarmanRegion

#print axioms FactoredDivisorHarmanRegion.eventually_region
run_cmd do
  for target in [``FactoredDivisorHarmanRegion.numeric_exponents,
      ``FactoredDivisorHarmanRegion.eta_properties,
      ``FactoredDivisorHarmanRegion.eventual_frequency_arithmetic,
      ``FactoredDivisorHarmanRegion.pair_total_guards,
      ``FactoredDivisorHarmanRegion.eventually_region,
      ``FactoredDivisorHarmanRegion.eventual_numeric_witness,
      ``FactoredDivisorHarmanRegion.eventually_point101] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice ||
          ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FACTORED DIVISOR HARMAN REGION PASSED"
