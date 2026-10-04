import OuterCenteredExceptionalWork

/-! Flat cancellation on the literal cofactor ratio, obtained by at most
12 dyadic pieces. No prime cancellation hypothesis is used. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
open Filter MeasureTheory Set
namespace OuterWideFlatCapWork
open Erdos374.HarmanGram152 OuterCenteredFlatWork

theorem dyadic_cover_bound (X L C σ t : ℝ) (hC : 0≤C)
    (hcap : ∀N lo hi : ℕ,L≤(N:ℝ) → (N:ℝ)≤X → N≤lo → hi≤2*N →
      ‖verticalDirichlet152 (Finset.Ioc lo hi) (fun _ => 1) σ t‖≤C)
    (J N hi : ℕ) (hN : L≤(N:ℝ)) (hNX : (N:ℝ)≤X) (hhiX : (hi:ℝ)≤X)
    (hwide : hi≤2^J*N) :
    ‖verticalDirichlet152 (Finset.Ioc N hi) (fun _ => 1) σ t‖≤(J:ℝ)*C := by
  induction J generalizing N with
  | zero =>
    have hh : hi≤N := by simpa using hwide
    have he : Finset.Ioc N hi=∅ := Finset.Ioc_eq_empty_of_le hh
    simp [he,verticalDirichlet152]
  | succ J ih =>
    by_cases hh : hi≤2*N
    · have hb := hcap N N hi hN hNX le_rfl hh
      apply hb.trans
      have : (1:ℝ)≤(J+1:ℕ) := by exact_mod_cast Nat.succ_pos J
      nlinarith
    · have h2 : 2*N≤hi := by omega
      have h2R : ((2*N:ℕ):ℝ)≤X := (by exact_mod_cast h2 : ((2*N:ℕ):ℝ)≤hi).trans hhiX
      have hL : L≤((2*N:ℕ):ℝ) := hN.trans (by exact_mod_cast (show N≤2*N by omega))
      have hwide' : hi≤2^J*(2*N) := by simpa only [pow_succ,Nat.mul_assoc] using hwide
      have hb := ih (2*N) hL h2R hwide'
      have hs : verticalDirichlet152 (Finset.Ioc N hi) (fun _ => 1) σ t=
          verticalDirichlet152 (Finset.Ioc N (2*N)) (fun _ => 1) σ t+
          verticalDirichlet152 (Finset.Ioc (2*N) hi) (fun _ => 1) σ t := by
        exact (Finset.sum_Ioc_consecutive _ (show N≤2*N by omega) h2).symm
      rw [hs]
      apply (norm_add_le _ _).trans
      have ha := hcap N N (2*N) hN hNX le_rfl le_rfl
      push_cast
      nlinarith

theorem eventually_wide_centered_cap (ε ρ : ℝ) (hε : 0<ε) (hρ : 0<ρ) (hρ1 : ρ≤1) :
    ∃κ : ℝ,0<κ ∧ κ≤ρ ∧ ∀ᶠ X : ℝ in atTop,1≤X ∧
      ∀(N hi : ℕ) (σ t : ℝ), X^ε≤(N:ℝ) → (hi:ℝ)≤X → N≤hi → hi≤2049*N →
        1≤σ → X^ρ≤|t| → |t|≤X → ‖centeredFlat N hi σ t‖≤14*X^(-κ) := by
  obtain ⟨κ,hκ,hκρ,hcap⟩ := FlatPowerCap.eventually_bound ε ρ ρ hε hρ hρ1 hρ
  refine ⟨κ,hκ,hκρ,?_⟩
  filter_upwards [hcap] with X hc
  refine ⟨hc.1,?_⟩
  intro N hi σ t hN hhiX hNhi hwide hσ ht htx
  have hXp : 0<X := by linarith [hc.1]
  have hN1 : 1≤N := by exact_mod_cast (Real.one_le_rpow hc.1 hε.le).trans hN
  have hNX : (N:ℝ)≤X := (by exact_mod_cast hNhi : (N:ℝ)≤hi).trans hhiX
  have hd := dyadic_cover_bound X (X^ε) (X^(-κ)) σ t (by positivity)
    (fun M lo hi hM hMX hlo hhi => hc.2 M lo hi hM hMX hlo hhi t σ ht htx hσ)
    12 N hi hN hNX hhiX (by norm_num; omega)
  have ht0 : 0 < |t| := (Real.rpow_pos_of_pos hXp _).trans_le ht
  have hcont : ‖continuousFlat N hi σ t‖≤2*X^(-κ) := by
    calc
      _ ≤ 2/|t| := continuousFlat_bound N hi σ t hN1 (hN1.trans hNhi) hσ ht0
      _ ≤ 2/(X^ρ) := div_le_div_of_nonneg_left (by norm_num) (by positivity) ht
      _ = 2*X^(-ρ) := by rw [Real.rpow_neg hXp.le,div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc.1 (by linarith)) (by norm_num)
  apply (norm_sub_le _ _).trans
  norm_num only [Nat.cast_ofNat] at hd
  linarith

run_cmd do
  for decl in [``dyadic_cover_bound, ``eventually_wide_centered_cap] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterWideFlatCapWork
