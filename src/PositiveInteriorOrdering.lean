import PositiveInteriorRectangles

/-! Source coordinates are u = log(P)/log(X), v = log(R)/log(X).
The third prime has limiting exponent 1-u-v.  This file proves exact
ordering margins and their stability under bounded logarithmic dyadic
perturbations.  It does not identify an arithmetic triple count. -/
set_option autoImplicit false
noncomputable section
namespace PositiveInteriorOrdering
open PositiveInteriorRectangles

def third (u v : ℝ) : ℝ := 1-u-v

theorem first_lower (u v : ℝ) (h : interior u v) : 447/1400 ≤ u := by
  rcases h with ⟨h1,h2,h3,h4⟩
  linarith

theorem third_upper (u v : ℝ) (h : interior u v) : third u v ≤ 8/35 := by
  rcases h with ⟨h1,h2,h3,h4⟩
  unfold third
  linarith

theorem first_gap (u v : ℝ) (h : interior u v) :
    127/1400 ≤ u-third u v := by
  have hu := first_lower u v h
  have hw := third_upper u v h
  linarith

theorem second_gap (u v : ℝ) (h : interior u v) :
    307/7000 ≤ v-third u v := by
  rcases h with ⟨h1,h2,h3,h4⟩
  unfold third
  linarith

theorem cubic_gap (u v : ℝ) (h : interior u v) :
    1/600 ≤ third u v-(1-u)/3 := by
  rcases h with ⟨h1,h2,h3,h4⟩
  unfold third
  linarith

theorem square_gap (u v : ℝ) (h : interior u v) :
    1/1000 ≤ 1/2-u := by
  rcases h with ⟨h1,h2,h3,h4⟩
  linarith

theorem cubic_product_gap (u v : ℝ) (h : interior u v) :
    1/200 ≤ 2-2*u-3*v := by
  rcases h with ⟨h1,h2,h3,h4⟩
  linarith

theorem limiting_order (u v : ℝ) (h : interior u v) :
    third u v < u ∧ third u v < v ∧ (1-u)/3 < third u v := by
  have h1 := first_gap u v h
  have h2 := second_gap u v h
  have h3 := cubic_gap u v h
  exact ⟨by linarith, by linarith, by linarith⟩

/-! If p/P and r/R lie in [1,2], write their exponent increments as
a,b in [0,h], h=log(2)/log(X).  If p*q*r lies in [X/2,2X], its normalized
logarithm is 1+c with c in [-h,h], so q has exponent third u v+c-a-b.
The following result uses precisely these perturbation hypotheses. -/
theorem dyadic_margins (u v a b c h : ℝ) (hi : interior u v)
    (hh : h ≤ 1/3200) (ha : 0 ≤ a ∧ a ≤ h) (hb : 0 ≤ b ∧ b ≤ h)
    (hc : -h ≤ c ∧ c ≤ h) :
    1/12 ≤ (u+a)-(third u v+c-a-b) ∧
    1/25 ≤ (v+b)-(third u v+c-a-b) ∧
    1/1200 ≤ (third u v+c-a-b)-(1-(u+a))/3 ∧
    11/16000 ≤ 1/2-(u+a) ∧
    87/1400 ≤ (u+a)-9/35 ∧
    1/7 ≤ third u v+c-a-b := by
  have h1 := first_gap u v hi
  have h2 := second_gap u v hi
  have h3 := cubic_gap u v hi
  have h4 := square_gap u v hi
  have h5 := first_lower u v hi
  have h6 := (component_bounds u v hi).2.2
  change 1/6 ≤ third u v at h6
  exact ⟨by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩

theorem dyadic_level_order (u v a b c h s : ℝ) (hi : interior u v)
    (hh : h ≤ 1/3200) (ha : 0 ≤ a ∧ a ≤ h) (hb : 0 ≤ b ∧ b ≤ h)
    (hc : -h ≤ c ∧ c ≤ h) (hs : 0 ≤ s) :
    third u v+c-a-b < u+a ∧
    third u v+c-a-b < v+b ∧
    (1-3*s-(u+a))/3 < third u v+c-a-b ∧
    u+a < 1/2 ∧ 9/35 < u+a := by
  obtain ⟨h1,h2,h3,h4,h5,h6⟩ := dyadic_margins u v a b c h hi hh ha hb hc
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

run_cmd do
  for decl in [``first_lower, ``third_upper, ``first_gap, ``second_gap,
      ``cubic_gap, ``square_gap, ``cubic_product_gap, ``limiting_order,
      ``dyadic_margins, ``dyadic_level_order] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "POSITIVE INTERIOR ORDERING: TEN EXACT COORDINATE GUARDS; NO ARITHMETIC TRANSFER"
end PositiveInteriorOrdering
end
