import FactoredDivisorWeights
import SieveUpperBoxWindow

/-! Collection of arbitrary complex weights on actual (p,d) representations.
The small carrier and each weight may depend on p. All collisions are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace ShortSingletonCollection

def index (a : ℕ × ℕ) : ℕ := a.1 * a.2

def support (S : Finset (ℕ × ℕ)) : Finset ℕ := S.image index

def coefficient (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ a ∈ S.filter (fun a => index a = n), w a

theorem fiber_card_le (S : Finset (ℕ × ℕ)) (n : ℕ) (hn : n ≠ 0) :
    (S.filter (fun a => index a = n)).card ≤ n.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro a ha
    have he := (Finset.mem_filter.mp ha).2
    exact Nat.mem_divisors.mpr ⟨⟨a.2, he.symm⟩, hn⟩
  · intro a ha b hb hab
    have hea := (Finset.mem_filter.mp ha).2
    have heb := (Finset.mem_filter.mp hb).2
    have hap : 0 < a.1 := by
      by_contra hp
      have hz : a.1 = 0 := by omega
      exact hn (by simpa [index, hz] using hea.symm)
    apply Prod.ext hab
    apply Nat.eq_of_mul_eq_mul_left hap
    simpa only [index, ←hab] using hea.trans heb.symm

theorem coefficient_norm_le (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ)
    (n : ℕ) (hn : n ≠ 0) (hw : ∀ a ∈ S, ‖w a‖ ≤ 1) :
    ‖coefficient S w n‖ ≤ (n.divisors.card : ℝ) := by
  calc
    _ ≤ ∑ a ∈ S.filter (fun a => index a = n), ‖w a‖ := norm_sum_le _ _
    _ ≤ ∑ _a ∈ S.filter (fun a => index a = n), (1 : ℝ) := by
      exact Finset.sum_le_sum (fun a ha => hw a (Finset.mem_filter.mp ha).1)
    _ = ((S.filter (fun a => index a = n)).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast fiber_card_le S n hn

theorem coefficient_zero_off_support (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ)
    (n : ℕ) (hn : n ∉ support S) : coefficient S w n = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  obtain ⟨ha,he⟩ := Finset.mem_filter.mp ha
  exact False.elim (hn (Finset.mem_image.mpr ⟨a,ha,he⟩))

theorem grouped_sum (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ) (f : ℕ → ℂ) :
    (∑ n ∈ support S, coefficient S w n * f n) =
      ∑ a ∈ S, w a * f (index a) := by
  unfold coefficient
  simp_rw [Finset.sum_mul]
  have hh := Finset.sum_fiberwise_of_maps_to
    (fun a (ha : a ∈ S) => show index a ∈ support S from Finset.mem_image.mpr ⟨a,ha,rfl⟩)
    (fun a => w a * f (index a))
  rw [←hh]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro a ha
  rw [(Finset.mem_filter.mp ha).2]

theorem eventual_coefficient_cap (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop, 1 ≤ X ∧
      ∀ (S : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℂ) (n : ℕ),
        0 < n → (n : ℝ) ≤ X^2 → (∀ a ∈ S, ‖w a‖ ≤ 1) →
        ‖coefficient S w n‖ ≤ X^δ := by
  obtain ⟨D,hD,hdiv⟩ := DivisorPowerBound.divisor_count_bound (δ/4) (by positivity)
  filter_upwards [PolynomialLogEnvelope.eventually_constant_bound D (δ/2)
    hD.le (by positivity)] with X hX
  refine ⟨hX.1,?_⟩
  intro S w n hn hnX hw
  have hXp : 0 < X := by linarith [hX.1]
  have hp : (n : ℝ)^(δ/4) ≤ X^(δ/2) := by
    calc
      _ ≤ (X^2)^(δ/4) := Real.rpow_le_rpow (Nat.cast_nonneg n) hnX (by positivity)
      _ = _ := by rw [←Real.rpow_natCast_mul hXp.le]; congr 1; ring
  calc
    _ ≤ (n.divisors.card : ℝ) := coefficient_norm_le S w n (by omega) hw
    _ ≤ D*(n:ℝ)^(δ/4) := hdiv n
    _ ≤ X^(δ/2)*X^(δ/2) := mul_le_mul hX.2 hp (by positivity) (by positivity)
    _ = X^δ := by rw [←Real.rpow_add hXp]; congr 1; ring

def representations (P : Finset ℕ) (D : ℕ → Finset ℕ) : Finset (ℕ × ℕ) :=
  P.biUnion (fun p => (D p).image (fun d => (p,d)))

theorem mem_representations (P : Finset ℕ) (D : ℕ → Finset ℕ) (p d : ℕ) :
    (p,d) ∈ representations P D ↔ p ∈ P ∧ d ∈ D p := by
  simp [representations]

theorem representation_sum (P : Finset ℕ) (D : ℕ → Finset ℕ)
    (f : ℕ × ℕ → ℂ) :
    (∑ a ∈ representations P D, f a) = ∑ p ∈ P, ∑ d ∈ D p, f (p,d) := by
  unfold representations
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro p _
    exact Finset.sum_image (fun a _ b _ hab => (Prod.mk.inj hab).2)
  · intro p _ q _ hpq
    apply Finset.disjoint_left.mpr
    intro a hp hq
    obtain ⟨d,_,hd⟩ := Finset.mem_image.mp hp
    obtain ⟨e,_,he⟩ := Finset.mem_image.mp hq
    exact hpq (Prod.mk.inj (hd.trans he.symm)).1

theorem dependent_grouped_sum (P : Finset ℕ) (D : ℕ → Finset ℕ)
    (w : ℕ × ℕ → ℂ) (f : ℕ → ℂ) :
    (∑ n ∈ support (representations P D), coefficient (representations P D) w n * f n) =
      ∑ p ∈ P, ∑ d ∈ D p, w (p,d) * f (p*d) := by
  rw [grouped_sum, representation_sum]
  rfl

theorem sieve_phase_cap (P : Finset ℕ) (D : ℕ → ℝ) (s : ℝ)
    (u v : ℕ → ℂ) (hu : ∀ p ∈ P, ‖u p‖ ≤ 1) (hv : ∀ n, ‖v n‖ ≤ 1)
    (n : ℕ) (hn : n ≠ 0) :
    ‖coefficient (representations P (fun p => SieveUpperBoxWindow.smallCarrier (D p) s))
      (fun a => (SieveSmallWeights.weight ((D a.1)^s) ((D a.1)^(s^2)) false a.2 : ℂ)
        * u a.1 * v (index a)) n‖ ≤ (n.divisors.card : ℝ) := by
  apply coefficient_norm_le _ _ n hn
  intro a ha
  obtain ⟨hp,_⟩ := (mem_representations P _ a.1 a.2).mp ha
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hw := SieveSmallWeights.weight_abs_le_one ((D a.1)^s) ((D a.1)^(s^2)) false a.2
  calc
    _ ≤ 1*1*1 := mul_le_mul
      (mul_le_mul hw (hu a.1 hp) (norm_nonneg _) (by norm_num))
      (hv (index a)) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

run_cmd do
  for decl in [``fiber_card_le, ``coefficient_norm_le, ``coefficient_zero_off_support,
      ``grouped_sum, ``eventual_coefficient_cap, ``mem_representations,
      ``representation_sum, ``dependent_grouped_sum, ``sieve_phase_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "DEPENDENT PRIME-DIVISOR COLLECTION AND UNIFORM SUBPOWER CAP PASSED"

end ShortSingletonCollection
