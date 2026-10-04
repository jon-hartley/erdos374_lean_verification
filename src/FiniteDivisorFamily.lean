import SignedDivisorRegularity

/-! Exact finite aggregation of signed divisor remainders and its square cost. -/

set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace FiniteDivisorFamily
open HarmanDivisorWindow

def support {ι : Type*} (family : Finset ι) (supports : ι → Finset ℕ) :
    Finset ℕ := family.biUnion supports

def coefficient {ι : Type*} (family : Finset ι)
    (supports : ι → Finset ℕ) (weights : ι → ℕ → ℝ) (d : ℕ) : ℝ :=
  ∑ i ∈ family, if d ∈ supports i then weights i d else 0

theorem sum_coefficient {ι : Type*} (family : Finset ι)
    (supports : ι → Finset ℕ) (weights : ι → ℕ → ℝ) (f : ℕ → ℝ) :
    (∑ d ∈ support family supports,
      coefficient family supports weights d * f d) =
      ∑ i ∈ family, ∑ d ∈ supports i, weights i d * f d := by
  classical
  calc
    _ = ∑ d ∈ support family supports,
          ∑ i ∈ family, if d ∈ supports i then weights i d * f d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [coefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp
    _ = ∑ i ∈ family, ∑ d ∈ support family supports,
          if d ∈ supports i then weights i d * f d else 0 := Finset.sum_comm
    _ = ∑ i ∈ family, ∑ d ∈ supports i, weights i d * f d := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsub : supports i ⊆ support family supports := by
        intro d hd
        exact Finset.mem_biUnion.mpr ⟨i, hi, hd⟩
      calc
        _ = ∑ d ∈ supports i,
              if d ∈ supports i then weights i d * f d else 0 := by
          symm
          apply Finset.sum_subset hsub
          intro d hd hdnot
          simp [hdnot]
        _ = _ := by simp

theorem remainder_eq_sum {ι : Type*} (family : Finset ι)
    (supports : ι → Finset ℕ) (weights : ι → ℕ → ℝ)
    (L R : ℝ) :
    remainder (support family supports) (coefficient family supports weights) L R =
      ∑ i ∈ family, remainder (supports i) (weights i) L R := by
  have hcount := sum_coefficient family supports weights
    (fun d => (⌊R / d⌋₊ : ℝ) - (⌊L / d⌋₊ : ℝ))
  have hmass := sum_coefficient family supports weights (fun d => (d : ℝ)⁻¹)
  have hcount' :
      divisorCount (support family supports) (coefficient family supports weights) L R =
        ∑ i ∈ family, divisorCount (supports i) (weights i) L R := by
    exact hcount
  have hmass' :
      reciprocalMass (support family supports) (coefficient family supports weights) =
        ∑ i ∈ family, reciprocalMass (supports i) (weights i) := by
    simp only [reciprocalMass, div_eq_mul_inv]
    exact hmass
  unfold remainder
  rw [hcount', hmass', Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]

theorem normalized_mean_square_bound {ι : Type*} (family : Finset ι)
    (supports : ι → Finset ℕ) (weights : ι → ℕ → ℝ)
    (X Y B : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (hYX : Y ≤ X)
    (_hB : 0 ≤ B)
    (hmean : ∀ i ∈ family,
      (1 / X) * (∫ x in Icc X (2 * X),
        remainder (supports i) (weights i) (x - x * (Y / X)) x ^ 2) ≤ B) :
    (1 / X) * (∫ x in Icc X (2 * X),
      remainder (support family supports) (coefficient family supports weights)
        (x - x * (Y / X)) x ^ 2) ≤ (family.card : ℝ) ^ 2 * B := by
  let δ : ℝ := Y / X
  have hδ : δ ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hY hX.le, (div_le_one hX).mpr hYX⟩
  let e := fun i x => remainder (supports i) (weights i) (x - x * δ) x
  have hInt (i : ι) (hi : i ∈ family) :
      IntegrableOn (fun x => e i x ^ 2) (Icc X (2 * X)) := by
    exact SignedDivisorRegularity.integrable_remainder_square
      (supports i) (weights i) X δ hX.le hδ
  have hCombined : IntegrableOn
      (fun x => remainder (support family supports)
        (coefficient family supports weights) (x - x * δ) x ^ 2)
      (Icc X (2 * X)) := by
    exact SignedDivisorRegularity.integrable_remainder_square
      (support family supports) (coefficient family supports weights)
      X δ hX.le hδ
  have hSum : IntegrableOn (fun x => ∑ i ∈ family, e i x ^ 2)
      (Icc X (2 * X)) := by
    change Integrable (fun x => ∑ i ∈ family, e i x ^ 2)
      (volume.restrict (Icc X (2 * X)))
    have hi := integrable_finsetSum' family hInt
    have heq : (∑ i ∈ family, fun x => e i x ^ 2) =
        (fun x => ∑ i ∈ family, e i x ^ 2) := by
      funext x
      simp only [Finset.sum_apply]
    rw [heq] at hi
    exact hi
  have hRhs : IntegrableOn (fun x =>
      (family.card : ℝ) * ∑ i ∈ family, e i x ^ 2)
      (Icc X (2 * X)) := hSum.const_mul _
  have hPoint (x : ℝ) :
      remainder (support family supports) (coefficient family supports weights)
        (x - x * δ) x ^ 2 ≤
        (family.card : ℝ) * ∑ i ∈ family, e i x ^ 2 := by
    rw [remainder_eq_sum]
    have hh := Finset.sum_mul_sq_le_sq_mul_sq family
      (fun i => e i x) (fun _ => (1 : ℝ))
    simpa [e, nsmul_eq_mul, mul_comm] using hh
  have hIntegral :
      (∫ x in Icc X (2 * X),
        remainder (support family supports) (coefficient family supports weights)
          (x - x * δ) x ^ 2) ≤
      ∫ x in Icc X (2 * X),
        (family.card : ℝ) * ∑ i ∈ family, e i x ^ 2 :=
    integral_mono hCombined hRhs hPoint
  calc
    _ ≤ (1 / X) * (∫ x in Icc X (2 * X),
        (family.card : ℝ) * ∑ i ∈ family, e i x ^ 2) :=
      mul_le_mul_of_nonneg_left hIntegral (by positivity)
    _ = (family.card : ℝ) *
        ∑ i ∈ family, (1 / X) * (∫ x in Icc X (2 * X), e i x ^ 2) := by
      rw [integral_const_mul, integral_finsetSum family hInt]
      simp only [← Finset.mul_sum]
      ring
    _ ≤ (family.card : ℝ) * ∑ _i ∈ family, B := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro i hi
        exact hmean i hi
      · exact_mod_cast Nat.zero_le family.card
    _ = (family.card : ℝ) ^ 2 * B := by
      simp [nsmul_eq_mul]
      ring

theorem normalized_power_bound {ι : Type*} (family : Finset ι)
    (supports : ι → Finset ℕ) (weights : ι → ℕ → ℝ)
    (X Y γ : ℝ) (hX : 0 < X) (hY : 0 ≤ Y) (hYX : Y ≤ X)
    (hcard : (family.card : ℝ) ≤ X ^ (γ / 4))
    (hmean : ∀ i ∈ family,
      (1 / X) * (∫ x in Icc X (2 * X),
        remainder (supports i) (weights i) (x - x * (Y / X)) x ^ 2) ≤
          Y ^ 2 * X ^ (-γ)) :
    (1 / X) * (∫ x in Icc X (2 * X),
      remainder (support family supports) (coefficient family supports weights)
        (x - x * (Y / X)) x ^ 2) ≤ Y ^ 2 * X ^ (-(γ / 2)) := by
  have hbase := normalized_mean_square_bound family supports weights X Y
    (Y ^ 2 * X ^ (-γ)) hX hY hYX (by positivity) hmean
  apply hbase.trans
  calc
    (family.card : ℝ) ^ 2 * (Y ^ 2 * X ^ (-γ)) ≤
        (X ^ (γ / 4)) ^ 2 * (Y ^ 2 * X ^ (-γ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 2
    _ = Y ^ 2 * X ^ (-(γ / 2)) := by
      rw [← Real.rpow_mul_natCast hX.le]
      calc
        _ = Y ^ 2 * (X ^ ((γ / 4) * (2 : ℕ)) * X ^ (-γ)) := by ring
        _ = Y ^ 2 * X ^ ((γ / 4) * (2 : ℕ) + -γ) := by
          rw [← Real.rpow_add hX]
        _ = _ := by congr 1; ring

end FiniteDivisorFamily

run_cmd do
  for target in [``FiniteDivisorFamily.sum_coefficient,
      ``FiniteDivisorFamily.remainder_eq_sum,
      ``FiniteDivisorFamily.normalized_mean_square_bound,
      ``FiniteDivisorFamily.normalized_power_bound] do
    let axioms ← Lean.collectAxioms target
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax}"
  Lean.logInfo "FINITE DIVISOR FAMILY PASSED"
