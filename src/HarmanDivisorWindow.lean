import DirichletProductCoefficients
import SmoothedCountBoundary

/-!
Exact signed divisor counts on (L,R]. Products retain their multiplicity
until grouped into one coefficient family. This extends the finite
convolution and sharp-count siblings; no asymptotic estimate or prime
main term is asserted. Natural floors are cast before subtraction.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators

namespace HarmanDivisorWindow
open Erdos374.HarmanGram152 DirichletProductCoefficients

/-- Finite signed divisor count with the lower endpoint excluded. -/
def divisorCount (s : Finset ℕ) (weight : ℕ → ℝ) (L R : ℝ) : ℝ :=
  ∑ d ∈ s, weight d * ((⌊R / d⌋₊ : ℝ) - (⌊L / d⌋₊ : ℝ))

def reciprocalMass (s : Finset ℕ) (weight : ℕ → ℝ) : ℝ :=
  ∑ d ∈ s, weight d / d

def remainder (s : Finset ℕ) (weight : ℕ → ℝ) (L R : ℝ) : ℝ :=
  divisorCount s weight L R - (R - L) * reciprocalMass s weight

def productSupport (s cofactors : Finset ℕ) : Finset ℕ :=
  (s ×ˢ cofactors).image productIndex

def coefficient (s cofactors : Finset ℕ) (weight : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ pair ∈ (s ×ˢ cofactors).filter (fun pair => productIndex pair = n),
    weight pair.1

def pairWindow (s cofactors : Finset ℕ) (weight : ℕ → ℝ) (L R : ℝ) : ℝ :=
  ∑ pair ∈ s ×ˢ cofactors,
    if L < (productIndex pair : ℝ) ∧ (productIndex pair : ℝ) ≤ R then
      weight pair.1 else 0

theorem cofactor_window_eq (d lo hi : ℕ) (L R : ℝ)
    (hd : 0 < d) (hL : 0 ≤ L) (hLR : L ≤ R)
    (hlo : lo ≤ ⌊L / d⌋₊) (hhi : ⌊R / d⌋₊ ≤ hi) :
    (Finset.Ioc lo hi).filter
      (fun k => L < ((d * k : ℕ) : ℝ) ∧ ((d * k : ℕ) : ℝ) ≤ R) =
        Finset.Ioc ⌊L / d⌋₊ ⌊R / d⌋₊ := by
  classical
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hLdiv : 0 ≤ L / d := div_nonneg hL hdp.le
  have hRdiv : 0 ≤ R / d := div_nonneg (hL.trans hLR) hdp.le
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.cast_mul]
  constructor
  · rintro ⟨_, hleft, hright⟩
    exact ⟨(Nat.floor_lt hLdiv).mpr ((div_lt_iff₀ hdp).mpr (by nlinarith)),
      (Nat.le_floor_iff hRdiv).mpr ((le_div_iff₀ hdp).mpr (by nlinarith))⟩
  · rintro ⟨hleft, hright⟩
    refine ⟨⟨hlo.trans_lt hleft, hright.trans hhi⟩, ?_, ?_⟩
    · have hh := (div_lt_iff₀ hdp).mp ((Nat.floor_lt hLdiv).mp hleft)
      nlinarith
    · have hh := (le_div_iff₀ hdp).mp ((Nat.le_floor_iff hRdiv).mp hright)
      nlinarith

theorem cofactor_count (d lo hi : ℕ) (L R w : ℝ)
    (hd : 0 < d) (hL : 0 ≤ L) (hLR : L ≤ R)
    (hlo : lo ≤ ⌊L / d⌋₊) (hhi : ⌊R / d⌋₊ ≤ hi) :
    w * ((⌊R / d⌋₊ : ℝ) - (⌊L / d⌋₊ : ℝ)) =
      ∑ k ∈ Finset.Ioc lo hi,
        if L < ((d * k : ℕ) : ℝ) ∧ ((d * k : ℕ) : ℝ) ≤ R then w else 0 := by
  classical
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor : ⌊L / d⌋₊ ≤ ⌊R / d⌋₊ :=
    Nat.floor_mono (div_le_div_of_nonneg_right hLR hdp.le)
  rw [← Finset.sum_filter, cofactor_window_eq d lo hi L R hd hL hLR hlo hhi]
  simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hfloor]
  ring

theorem divisorCount_eq_pairWindow (s : Finset ℕ) (weight : ℕ → ℝ)
    (lo hi : ℕ) (L R : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hL : 0 ≤ L) (hLR : L ≤ R)
    (hlo : ∀ d ∈ s, lo ≤ ⌊L / d⌋₊)
    (hhi : ∀ d ∈ s, ⌊R / d⌋₊ ≤ hi) :
    divisorCount s weight L R = pairWindow s (Finset.Ioc lo hi) weight L R := by
  unfold divisorCount pairWindow
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  exact cofactor_count d lo hi L R (weight d) (hs d hd) hL hLR (hlo d hd) (hhi d hd)

theorem floor_div_le_common_cutoff (d B : ℕ) (R : ℝ)
    (hd : 0 < d) (hR : 0 ≤ R) (hB : R ≤ (B : ℝ)) : ⌊R / d⌋₊ ≤ B := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdiv : R / d ≤ R := div_le_self hR hd1
  exact_mod_cast (Nat.floor_le (div_nonneg hR (by positivity : (0 : ℝ) ≤ d))).trans
    (hdiv.trans hB)

theorem divisorCount_eq_pairWindow_common (s : Finset ℕ) (weight : ℕ → ℝ)
    (B : ℕ) (L R : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hB : R ≤ (B : ℝ)) :
    divisorCount s weight L R = pairWindow s (Finset.Ioc 0 B) weight L R :=
  divisorCount_eq_pairWindow s weight 0 B L R hs hL hLR
    (fun _ _ => Nat.zero_le _) (fun d hd =>
      floor_div_le_common_cutoff d B R (hs d hd) (hL.trans hLR) hB)

/-- A lower bound on d gives a tighter common cofactor cutoff. -/
theorem floor_div_le_scale (M d : ℕ) (R : ℝ)
    (hM : 0 < M) (hMd : M ≤ d) (hR : 0 ≤ R) :
    ⌊R / d⌋₊ ≤ ⌊R / M⌋₊ := by
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_left hR
    (by exact_mod_cast hM : (0 : ℝ) < M)
    (by exact_mod_cast hMd : (M : ℝ) ≤ d)

theorem coefficient_cast (s cofactors : Finset ℕ) (weight : ℕ → ℝ) (n : ℕ) :
    (coefficient s cofactors weight n : ℂ) =
      DirichletProductCoefficients.coefficient s cofactors
        (fun d => (weight d : ℂ)) (fun _ => 1) n := by
  simp [coefficient, DirichletProductCoefficients.coefficient, pairWeight,
    Complex.ofReal_sum]

theorem grouped_sum (s cofactors target : Finset ℕ) (weight kernel : ℕ → ℝ)
    (hmap : ∀ pair ∈ s ×ˢ cofactors, productIndex pair ∈ target) :
    (∑ n ∈ target, coefficient s cofactors weight n * kernel n) =
      ∑ pair ∈ s ×ˢ cofactors, weight pair.1 * kernel (productIndex pair) := by
  apply Complex.ofReal_injective
  have hh := DirichletProductCoefficients.grouped_sum s cofactors target
    (fun d => (weight d : ℂ)) (fun _ => 1) (fun n => (kernel n : ℂ)) hmap
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, coefficient_cast,
    pairWeight, mul_one] using hh

theorem productSupport_contains (s cofactors : Finset ℕ)
    (pair : ℕ × ℕ) (hp : pair ∈ s ×ˢ cofactors) :
    productIndex pair ∈ productSupport s cofactors :=
  Finset.mem_image.mpr ⟨pair, hp, rfl⟩

theorem productSupport_positive (s cofactors : Finset ℕ)
    (hs : ∀ d ∈ s, 0 < d) (hc : ∀ k ∈ cofactors, 0 < k)
    (n : ℕ) (hn : n ∈ productSupport s cofactors) : 0 < n := by
  obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hd, hk⟩ := Finset.mem_product.mp hp
  exact Nat.mul_pos (hs pair.1 hd) (hc pair.2 hk)

theorem productSupport_le (s cofactors : Finset ℕ) (D B : ℕ)
    (hs : ∀ d ∈ s, d ≤ D) (hc : ∀ k ∈ cofactors, k ≤ B)
    (n : ℕ) (hn : n ∈ productSupport s cofactors) : n ≤ D * B := by
  obtain ⟨pair, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hd, hk⟩ := Finset.mem_product.mp hp
  exact Nat.mul_le_mul (hs pair.1 hd) (hc pair.2 hk)

theorem sharp_window (s : Finset ℕ) (weight : ℕ → ℝ) (L R : ℝ) (hLR : L ≤ R) :
    SmoothedCountBoundary.sharp s weight R - SmoothedCountBoundary.sharp s weight L =
      ∑ n ∈ s, if L < (n : ℝ) ∧ (n : ℝ) ≤ R then weight n else 0 := by
  classical
  unfold SmoothedCountBoundary.sharp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hnL : (n : ℝ) ≤ L
  · have hnR : (n : ℝ) ≤ R := hnL.trans hLR
    simp [hnL, hnR, not_lt.mpr hnL]
  · have hnL' : L < (n : ℝ) := lt_of_not_ge hnL
    by_cases hnR : (n : ℝ) ≤ R <;> simp [hnL, hnL', hnR]

theorem pairWindow_eq_sharp (s cofactors target : Finset ℕ) (weight : ℕ → ℝ)
    (L R : ℝ) (hLR : L ≤ R)
    (hmap : ∀ pair ∈ s ×ˢ cofactors, productIndex pair ∈ target) :
    pairWindow s cofactors weight L R =
      SmoothedCountBoundary.sharp target (coefficient s cofactors weight) R -
        SmoothedCountBoundary.sharp target (coefficient s cofactors weight) L := by
  classical
  rw [sharp_window target _ L R hLR]
  have hh := grouped_sum s cofactors target weight
    (fun n => if L < (n : ℝ) ∧ (n : ℝ) ≤ R then 1 else 0) hmap
  simpa only [mul_ite, mul_one, mul_zero, pairWindow] using hh.symm

theorem divisorCount_eq_sharp (s : Finset ℕ) (weight : ℕ → ℝ)
    (lo hi : ℕ) (L R : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hL : 0 ≤ L) (hLR : L ≤ R)
    (hlo : ∀ d ∈ s, lo ≤ ⌊L / d⌋₊)
    (hhi : ∀ d ∈ s, ⌊R / d⌋₊ ≤ hi) :
    divisorCount s weight L R =
      SmoothedCountBoundary.sharp (productSupport s (Finset.Ioc lo hi))
        (coefficient s (Finset.Ioc lo hi) weight) R -
      SmoothedCountBoundary.sharp (productSupport s (Finset.Ioc lo hi))
        (coefficient s (Finset.Ioc lo hi) weight) L := by
  rw [divisorCount_eq_pairWindow s weight lo hi L R hs hL hLR hlo hhi]
  exact pairWindow_eq_sharp s (Finset.Ioc lo hi) _ weight L R hLR
    (productSupport_contains _ _)

theorem divisorCount_eq_sharp_common (s : Finset ℕ) (weight : ℕ → ℝ)
    (B : ℕ) (L R : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hB : R ≤ (B : ℝ)) :
    divisorCount s weight L R =
      SmoothedCountBoundary.sharp (productSupport s (Finset.Ioc 0 B))
        (coefficient s (Finset.Ioc 0 B) weight) R -
      SmoothedCountBoundary.sharp (productSupport s (Finset.Ioc 0 B))
        (coefficient s (Finset.Ioc 0 B) weight) L := by
  rw [divisorCount_eq_pairWindow_common s weight B L R hs hL hLR hB]
  exact pairWindow_eq_sharp s (Finset.Ioc 0 B) _ weight L R hLR
    (productSupport_contains _ _)

theorem remainder_eq_sum (s : Finset ℕ) (weight : ℕ → ℝ) (L R : ℝ) :
    remainder s weight L R = ∑ d ∈ s, weight d *
      ((⌊R / d⌋₊ : ℝ) - (⌊L / d⌋₊ : ℝ) - (R - L) / d) := by
  unfold remainder divisorCount reciprocalMass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

theorem centered_identity (s : Finset ℕ) (weight : ℕ → ℝ)
    (lo hi : ℕ) (L R : ℝ) (hs : ∀ d ∈ s, 0 < d)
    (hL : 0 ≤ L) (hLR : L ≤ R)
    (hlo : ∀ d ∈ s, lo ≤ ⌊L / d⌋₊)
    (hhi : ∀ d ∈ s, ⌊R / d⌋₊ ≤ hi) :
    remainder s weight L R =
      SmoothedCountBoundary.sharp (productSupport s (Finset.Ioc lo hi))
        (coefficient s (Finset.Ioc lo hi) weight) R -
      SmoothedCountBoundary.sharp (productSupport s (Finset.Ioc lo hi))
        (coefficient s (Finset.Ioc lo hi) weight) L -
      (R - L) * reciprocalMass s weight := by
  unfold remainder
  rw [divisorCount_eq_sharp s weight lo hi L R hs hL hLR hlo hhi]

/-- The grouped polynomial equals the product for a common cofactor support. -/
theorem vertical_product (s cofactors target : Finset ℕ) (weight : ℕ → ℝ)
    (σ t : ℝ) (hmap : ∀ pair ∈ s ×ˢ cofactors, productIndex pair ∈ target) :
    verticalDirichlet152 target (fun n => (coefficient s cofactors weight n : ℂ)) σ t =
      verticalDirichlet152 s (fun d => (weight d : ℂ)) σ t *
        verticalDirichlet152 cofactors (fun _ => 1) σ t := by
  unfold verticalDirichlet152
  simp_rw [coefficient_cast]
  rw [DirichletProductCoefficients.grouped_sum s cofactors target
    (fun d => (weight d : ℂ)) (fun _ => 1)
    (fun n => (n : ℂ) ^ (-((σ : ℂ) + Complex.I * (t : ℂ)))) hmap,
    Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro k _
  simp only [pairWeight, productIndex, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, one_mul, mul_one]
  ring

theorem vertical_product_support (s cofactors : Finset ℕ) (weight : ℕ → ℝ)
    (σ t : ℝ) :
    verticalDirichlet152 (productSupport s cofactors)
      (fun n => (coefficient s cofactors weight n : ℂ)) σ t =
      verticalDirichlet152 s (fun d => (weight d : ℂ)) σ t *
        verticalDirichlet152 cofactors (fun _ => 1) σ t :=
  vertical_product s cofactors _ weight σ t (productSupport_contains _ _)

end HarmanDivisorWindow

#print axioms HarmanDivisorWindow.divisorCount_eq_sharp
#print axioms HarmanDivisorWindow.vertical_product_support
run_cmd do
  for target in [``HarmanDivisorWindow.cofactor_window_eq,
      ``HarmanDivisorWindow.divisorCount_eq_pairWindow_common,
      ``HarmanDivisorWindow.floor_div_le_scale,
      ``HarmanDivisorWindow.productSupport_positive,
      ``HarmanDivisorWindow.productSupport_le,
      ``HarmanDivisorWindow.divisorCount_eq_sharp_common,
      ``HarmanDivisorWindow.remainder_eq_sum,
      ``HarmanDivisorWindow.centered_identity,
      ``HarmanDivisorWindow.vertical_product_support] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "HARMAN DIVISOR WINDOW PASSED"
