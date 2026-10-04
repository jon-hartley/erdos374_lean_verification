import Item1RetainedKusmin
import Item1FiniteAbelPhase
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Actual specialization of the retained Kusmin--Landau theorem.
This covers M >= t only. It does NOT assert the required estimate for M < t.
The imported retained declaration is a proof body, not a phase-bound axiom. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators
namespace Item1LongLogPhase
open Item1FiniteAbelPhase

def logStep (x : ℝ) : ℝ := Real.log (x+1)-Real.log x

theorem logStep_bounds (x : ℝ) (hx : 0<x) :
    1/(x+1) ≤ logStep x ∧ logStep x ≤ 1/x := by
  have hxp : 0<x+1 := by linarith
  have hr : 0<(x+1)/x := div_pos hxp hx
  have hlog : Real.log ((x+1)/x)=logStep x := by
    rw [Real.log_div hxp.ne' hx.ne']; rfl
  have hl := Real.one_sub_inv_le_log_of_pos hr
  have hu := Real.log_le_sub_one_of_pos hr
  rw [hlog] at hl hu
  have hleft : 1-((x+1)/x)⁻¹=1/(x+1) := by field_simp; ring
  have hright : (x+1)/x-1=1/x := by field_simp; ring
  rw [hleft] at hl
  rw [hright] at hu
  exact ⟨hl,hu⟩

theorem logStep_antitone (x y : ℝ) (hx : 0<x) (hxy : x≤y) :
    logStep y≤logStep x := by
  have hy : 0<y := hx.trans_le hxy
  have hx1 : 0<x+1 := by linarith
  have hy1 : 0<y+1 := by linarith
  unfold logStep
  rw [←Real.log_div hy1.ne' hy.ne', ←Real.log_div hx1.ne' hx.ne']
  apply Real.log_le_log (div_pos hy1 hy)
  apply (div_le_div_iff₀ hy hx).mpr
  nlinarith

def phase (M : ℕ) (t : ℝ) (n : ℕ) : ℝ :=
  t/(2*Real.pi)*Real.log ((M:ℝ)+n)

def sep (M : ℕ) (t : ℝ) : ℝ := t/(4*Real.pi*(M:ℝ))

theorem phase_step (M n : ℕ) (t : ℝ) :
    phase M t (n+1)-phase M t n =
      t/(2*Real.pi)*logStep ((M:ℝ)+n) := by
  simp only [phase,logStep,Nat.cast_add,Nat.cast_one]
  ring

theorem phase_data (M K : ℕ) (t : ℝ) (hM : 1≤M)
    (ht : 0<t) (htM : t≤M) (hK : K≤M) :
    0<sep M t ∧ sep M t≤1/2 ∧
    (∀ n<K, sep M t≤phase M t (n+1)-phase M t n ∧
      phase M t (n+1)-phase M t n≤1-sep M t) ∧
    AntitoneOn (fun n => phase M t (n+1)-phase M t n) (Set.Iio K) := by
  have hMp : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hp : 0<Real.pi := Real.pi_pos
  have hs : 0<t/(2*Real.pi) := by positivity
  have hd : 0<sep M t := by unfold sep; positivity
  have hdh : sep M t≤1/2 := by
    unfold sep
    apply (div_le_iff₀ (by positivity : 0<4*Real.pi*(M:ℝ))).mpr
    have hpi : 1≤Real.pi := by linarith [Real.two_le_pi]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hMp.le]
  refine ⟨hd,hdh,?_,?_⟩
  · intro n hn
    have hnx : 0<(M:ℝ)+n := by positivity
    have hnM : (n:ℝ)+1≤M := by exact_mod_cast (by omega : n+1≤M)
    have hden : (M:ℝ)+n+1≤2*M := by nlinarith
    obtain ⟨hlo,hhi⟩ := logStep_bounds ((M:ℝ)+n) hnx
    have hlo' : 1/(2*(M:ℝ))≤logStep ((M:ℝ)+n) := by
      apply le_trans _ hlo
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    have hhi' : logStep ((M:ℝ)+n)≤1/(M:ℝ) := by
      apply hhi.trans
      apply (div_le_div_iff₀ hnx hMp).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    rw [phase_step]
    constructor
    · have hh := mul_le_mul_of_nonneg_left hlo' hs.le
      convert hh using 1 <;> dsimp [sep] <;> field_simp <;> ring
    · have hh := mul_le_mul_of_nonneg_left hhi' hs.le
      have hub : t/(2*Real.pi)*(1/(M:ℝ))≤1/2 := by
        have hpi : 1≤Real.pi := by linarith [Real.two_le_pi]
        have : t≤Real.pi*(M:ℝ) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hpi) hMp.le]
        rw [mul_one_div, div_div]
        apply (div_le_iff₀ (by positivity : 0<(2*Real.pi)*(M:ℝ))).mpr
        nlinarith
      linarith
  · intro m hm n hn hmn
    dsimp only
    rw [phase_step,phase_step]
    apply mul_le_mul_of_nonneg_left _ hs.le
    apply logStep_antitone _ _ (by positivity)
    exact_mod_cast Nat.add_le_add_left hmn M

/-- A literal, unweighted negative-log-phase sum on every prefix. -/
def atom (M : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((-t*Real.log ((M:ℝ)+n):ℝ):ℂ)*Complex.I)

theorem atom_eq_character (M n : ℕ) (t : ℝ) :
    atom M t n = Erdos374.KusminLandau151.e (-phase M t n) := by
  have hf : 2*Real.pi*(-phase M t n) = -t*Real.log ((M:ℝ)+n) := by
    dsimp [phase]
    field_simp
  unfold atom Erdos374.KusminLandau151.e
  rw [hf]

/-- Actual theorem call with k=-1: no unjustified deletion or evenness step. -/
theorem long_prefix_bound (M K : ℕ) (t : ℝ) (hM : 1≤M)
    (ht : 0<t) (htM : t≤M) (hK : K≤M) :
    ‖«prefix» (atom M t) K‖≤32*(M:ℝ)/t := by
  obtain ⟨hd,hdh,hinc,hm⟩ := phase_data M K t hM ht htM hK
  have hh := Erdos374.KusminLandau151.kusmin_landau_integer K
    (fun n => -phase M t n) (sep M t) (-1) hd hdh (by
      intro n hn
      obtain ⟨hlo,hhi⟩ := hinc n hn
      norm_num
      constructor <;> linarith) (Or.inl (by
      intro m hmK n hnK hmn
      have hh := hm hmK hnK hmn
      dsimp only
      linarith))
  have hp : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  have hid : 2/sep M t=8*Real.pi*(M:ℝ)/t := by
    unfold sep; field_simp; ring
  have hfinal : 8*Real.pi*(M:ℝ)/t≤32*(M:ℝ)/t := by
    apply div_le_div_of_nonneg_right _ ht.le
    nlinarith [mul_nonneg (by linarith [Real.pi_le_four] : 0≤4-Real.pi) hp.le]
  have hatom : «prefix» (atom M t) K =
      ∑ n ∈ Finset.range K, Erdos374.KusminLandau151.e (-phase M t n) := by
    unfold «prefix»
    exact Finset.sum_congr rfl (fun n _ => atom_eq_character M n t)
  rw [hatom]
  rw [hid] at hh
  exact hh.trans hfinal

/-- The real weights are decreasing for every nonnegative sigma. -/
theorem power_weights_antitone (M : ℕ) (sigma : ℝ) (hM : 1≤M)
    (hs : 0≤sigma) : Antitone (fun n : ℕ => ((M:ℝ)+n)^(-sigma)) := by
  have hMp : (0:ℝ)<M := by exact_mod_cast (by omega : 0<M)
  intro m n hmn
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
  exact_mod_cast Nat.add_le_add_left hmn M

theorem long_weighted_bound (M K : ℕ) (t sigma : ℝ) (hM : 1≤M)
    (ht : 0<t) (htM : t≤M) (hK : K≤M) (hs : 0≤sigma) :
    ‖∑ n ∈ Finset.range K, ((((M:ℝ)+n)^(-sigma):ℝ):ℂ)*atom M t n‖
      ≤ (32*(M:ℝ)/t)*(M:ℝ)^(-sigma) := by
  have hh := weighted_prefix_bound (atom M t)
    (fun n => ((M:ℝ)+n)^(-sigma)) K (32*(M:ℝ)/t)
    (by positivity) (fun n => Real.rpow_nonneg (by positivity) _)
    (power_weights_antitone M sigma hM hs)
    (fun k hk => long_prefix_bound M k t hM ht htM (hk.trans hK))
  simpa using hh

end Item1LongLogPhase

run_cmd do
  for target in [``Item1LongLogPhase.logStep_bounds, ``Item1LongLogPhase.logStep_antitone,
    ``Item1LongLogPhase.phase_step, ``Item1LongLogPhase.phase_data,
    ``Item1LongLogPhase.atom_eq_character, ``Item1LongLogPhase.long_prefix_bound,
    ``Item1LongLogPhase.power_weights_antitone, ``Item1LongLogPhase.long_weighted_bound] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"

#print axioms Item1LongLogPhase.long_prefix_bound
#print axioms Item1LongLogPhase.long_weighted_bound
