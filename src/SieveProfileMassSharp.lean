import SieveProfileMass

/-! A sharper constant keeps the s^9 collision saving after summing all profiles. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
open scoped BigOperators
namespace SieveProfileMass

theorem inverse_le_exp_sharp (w : ℝ) (hw : 0 ≤ w) (hwb : w ≤ 1/17) :
    1/(1-w) ≤ Real.exp ((17/16)*w) := by
  have hpos : 0 < 1-w := by linarith
  have hrat : 1/(1-w) ≤ 1+(17/16)*w := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [mul_nonneg hw (show 0 ≤ 1-17*w by linarith)]
  exact hrat.trans (by simpa only [add_comm] using Real.add_one_le_exp ((17/16)*w))

theorem product_inverse_le_exp_sharp (m : ℕ) (w : ℕ → ℝ)
    (hw : ∀ i < m, 0 ≤ w i) (hwb : ∀ i < m, w i ≤ 1/17) :
    (∏ i : Fin m, 1/(1-w i.val)) ≤
      Real.exp ((17/16) * ∑ i ∈ Finset.range m, w i) := by
  calc
    _ ≤ ∏ i : Fin m, Real.exp ((17/16)*w i.val) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact div_nonneg zero_le_one (by linarith [hwb i.val i.isLt])
      · intro i _
        exact inverse_le_exp_sharp _ (hw i.val i.isLt) (hwb i.val i.isLt)
    _ = _ := by
      rw [← Real.exp_sum, ← Finset.mul_sum, Fin.sum_univ_eq_sum_range]

theorem sorted_mass_le_exp_sharp (A : Finset (List ℕ)) (m K : ℕ) (w : ℕ → ℝ)
    (hlen : ∀ t ∈ A, t.length ≤ K) (hr : ∀ t ∈ A, ∀ i ∈ t, i < m)
    (ho : ∀ t ∈ A, t.Pairwise (· ≥ ·)) (hw : ∀ i < m, 0 ≤ w i)
    (hwb : ∀ i < m, w i ≤ 1/17) :
    (∑ t ∈ A, (t.map w).prod) ≤
      Real.exp ((17/16) * ∑ i ∈ Finset.range m, w i) :=
  (sorted_mass_le_product A m K w hlen hr ho hw
    (fun i hi => (hwb i hi).trans_lt (by norm_num))).trans
      (product_inverse_le_exp_sharp m w hw hwb)

run_cmd do
  for decl in [``inverse_le_exp_sharp, ``product_inverse_le_exp_sharp,
      ``sorted_mass_le_exp_sharp] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end SieveProfileMass
end
