import Item1RampSumDefinitions
import Mathlib.Tactic

/-!
Literal [N,2N) Mangoldt desmoothing. Both arithmetic endpoints
are included in the CLOSED error strips. The coefficient bound is applied
only after restricting to N <= n+1 <= 4N, not to all positive integers.
No PNT, zeta-strip, oscillatory cap, or endpoint-count premise is accepted.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
open scoped BigOperators
namespace Item1SharpDyadicSmoothing
open Item1LogRampSmoothing Item1RampDirichlet

/-- Positive-index exponential convention matching the actual contour sum. -/
def term (t : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp (-((1:ℂ)+(t:ℂ)*Complex.I)*(Real.log (n:ℝ):ℂ))

def dyadic (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico N (2*N), term t n

/-- Same n+1 indexing as the parent smoothFinite. -/
def domain (N : ℕ) : Finset ℕ := Finset.Ico (N-1) (4*N)

theorem coefficient_eq_term (t : ℝ) (n : ℕ) : coefficient t n = term t (n+1) := rfl

theorem domain_bounds (N n : ℕ) (hN : 1 ≤ N) (hn : n ∈ domain N) :
    N ≤ n+1 ∧ n+1 ≤ 4*N := by
  simp only [domain,Finset.mem_Ico] at hn
  omega

theorem exp_position (N : ℝ) (hN : 0 < N) (n : ℕ) :
    Real.exp (position N n) = (n+1:ℕ)/N := by
  rw [position,Real.exp_sub,Real.exp_log (by positivity),Real.exp_log hN]

theorem sharp_membership (N n : ℕ) (hN : 1 ≤ N) :
    (0 ≤ position (N:ℝ) n ∧ position (N:ℝ) n < Real.log 2) ↔
      n+1 ∈ Finset.Ico N (2*N) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hnp : (0:ℝ) < (n+1:ℕ) := by positivity
  have hlo := Real.log_le_log_iff hNr hnp
  have hhi := Real.log_lt_log_iff hnp (show 0<2*(N:ℝ) by positivity)
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hNr.ne'] at hhi
  simp only [position,Finset.mem_Ico]
  constructor
  · rintro ⟨ha,hb⟩
    have ha' : (N:ℝ) ≤ (n+1:ℕ) := hlo.mp (by linarith)
    have hb' : ((n+1:ℕ):ℝ) < ((2*N:ℕ):ℝ) := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hhi.mp (by linarith)
    exact ⟨by exact_mod_cast ha',by exact_mod_cast hb'⟩
  · rintro ⟨ha,hb⟩
    have ha' : (N:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast ha
    have hb' : ((n+1:ℕ):ℝ) < 2*(N:ℝ) := by exact_mod_cast hb
    have hla := hlo.mpr ha'
    have hlb := hhi.mpr hb'
    constructor <;> linarith

/-- The sharp weighted sum uses EXACTLY the original half-open interval. -/
theorem sharp_on_domain (N : ℕ) (hN : 1 ≤ N) (t : ℝ) :
    (∑ n ∈ domain N, coefficient t n*(sharp (Real.log 2) (position (N:ℝ) n):ℂ))
      = dyadic N t := by
  classical
  have hpoint (n : ℕ) :
      coefficient t n*(sharp (Real.log 2) (position (N:ℝ) n):ℂ) =
      if n+1 ∈ Finset.Ico N (2*N) then coefficient t n else 0 := by
    simp only [sharp,sharp_membership N n hN]
    split_ifs <;> simp
  simp_rw [hpoint]
  rw [←Finset.sum_filter]
  unfold dyadic
  apply Finset.sum_bij (fun n _ => n+1)
  · intro n hn
    exact (Finset.mem_filter.mp hn).2
  · intro n hn m hm he
    omega
  · intro m hm
    have hm1 : 1 ≤ m := hN.trans (Finset.mem_Ico.mp hm).1
    refine ⟨m-1,?_,by omega⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp only [domain,Finset.mem_Ico]
      have hml := (Finset.mem_Ico.mp hm).1
      have hmh := (Finset.mem_Ico.mp hm).2
      constructor <;> omega
    · simpa only [Nat.sub_add_cancel hm1] using hm
  · intro n _
    rfl

/-- The discarded lower indices have zero smoothed weight. No term near N is dropped. -/
theorem smooth_on_domain (N : ℕ) (hN : 1 ≤ N) (δ t : ℝ)
    (hδ : 0 < δ) :
    (∑ n ∈ domain N, coefficient t n*(weight (Real.log 2) δ (position (N:ℝ) n):ℂ))
      = smoothFinite (N:ℝ) δ t := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hs : domain N ⊆ Finset.range (4*N) := by
    intro n hn
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hn).2
  have hceil : Nat.ceil (4*(N:ℝ)) = 4*N := by
    rw [show 4*(N:ℝ)=((4*N:ℕ):ℝ) by norm_num,Nat.ceil_natCast]
  unfold smoothFinite
  rw [hceil]
  apply Finset.sum_subset hs
  intro n hn hnot
  have hnlt : n < N-1 := by
    have hhi := Finset.mem_range.mp hn
    simp only [domain,Finset.mem_Ico,not_and,not_le] at hnot
    omega
  have hnN : n+1 ≤ N := by omega
  have hlog := Real.log_le_log (show (0:ℝ)<(n+1:ℕ) by positivity)
    (show ((n+1:ℕ):ℝ)≤N by exact_mod_cast hnN)
  have hw := weight_left (Real.log 2) δ (position (N:ℝ) n)
    (Real.log_nonneg (by norm_num)) hδ (by unfold position; linarith)
  simp only [hw,Complex.ofReal_zero,mul_zero]

theorem coefficient_norm (t : ℝ) (n : ℕ) :
    ‖coefficient t n‖ = ArithmeticFunction.vonMangoldt (n+1)/(n+1:ℕ) := by
  have hn : (0:ℝ) < (n+1:ℕ) := by positivity
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n:=n+1)
  simp only [coefficient,norm_mul,Complex.norm_exp,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg hΛ]
  simp only [Complex.mul_re,Complex.neg_re,Complex.add_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    mul_zero,zero_mul,sub_zero,zero_add,mul_one,one_mul]
  simp only [add_zero,neg_one_mul]
  rw [Real.exp_neg,Real.exp_log hn]
  rfl

theorem coefficient_bound (N n : ℕ) (hN : 1 ≤ N) (t : ℝ)
    (hn : n ∈ domain N) : ‖coefficient t n‖ ≤ Real.log (4*(N:ℝ))/(N:ℝ) := by
  obtain ⟨hlo,hhi⟩ := domain_bounds N n hN hn
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hnp : (0:ℝ) < (n+1:ℕ) := by positivity
  have hlog := (ArithmeticFunction.vonMangoldt_le_log (n:=n+1)).trans
    (Real.log_le_log hnp (show ((n+1:ℕ):ℝ)≤4*(N:ℝ) by exact_mod_cast hhi))
  rw [coefficient_norm]
  exact div_le_div₀ ((ArithmeticFunction.vonMangoldt_nonneg (n:=n+1)).trans hlog) hlog hNr
    (show (N:ℝ)≤(n+1:ℕ) by exact_mod_cast hlo)

/-- Counting a finite collection of distinct shifted integers in [k,b]. -/
theorem shifted_card_le (s : Finset ℕ) (k : ℕ) (b : ℝ)
    (hkb : (k:ℝ) ≤ b)
    (hs : ∀ n ∈ s, k ≤ n+1 ∧ ((n+1:ℕ):ℝ) ≤ b) :
    (s.card:ℝ) ≤ b-(k:ℝ)+1 := by
  classical
  have hb0 : 0 ≤ b := (Nat.cast_nonneg k).trans hkb
  have hkfloor : k ≤ Nat.floor b := Nat.le_floor hkb
  have himage : s.image (fun n => n+1) ⊆ Finset.Icc k (Nat.floor b) := by
    intro m hm
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hm
    exact Finset.mem_Icc.mpr ⟨(hs n hn).1,Nat.le_floor (hs n hn).2⟩
  have hcard := Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ (by intro n m h; exact Nat.add_right_cancel h),Nat.card_Icc] at hcard
  have hreal : (s.card:ℝ) ≤ ((Nat.floor b+1-k:ℕ):ℝ) := by
    exact_mod_cast hcard
  rw [Nat.cast_sub (by omega : k≤Nat.floor b+1),Nat.cast_add,Nat.cast_one] at hreal
  linarith [Nat.floor_le hb0]

theorem edge_coordinate_bounds (N n : ℕ) (hN : 1 ≤ N) (δ : ℝ) :
    (position (N:ℝ) n ∈ Set.Icc 0 δ →
      N ≤ n+1 ∧ ((n+1:ℕ):ℝ) ≤ (N:ℝ)*Real.exp δ) ∧
    (position (N:ℝ) n ∈ Set.Icc (Real.log 2) (Real.log 2+δ) →
      2*N ≤ n+1 ∧ ((n+1:ℕ):ℝ) ≤ 2*(N:ℝ)*Real.exp δ) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have he := exp_position (N:ℝ) hNr n
  constructor
  · intro hh
    have hl := Real.exp_le_exp.mpr hh.1
    have hu := Real.exp_le_exp.mpr hh.2
    rw [Real.exp_zero,he] at hl
    rw [he] at hu
    refine ⟨?_,?_⟩
    · have := (le_div_iff₀ hNr).mp hl
      have hreal : (N:ℝ) ≤ (n+1:ℕ) := by simpa only [one_mul] using this
      exact_mod_cast hreal
    · have := (div_le_iff₀ hNr).mp hu
      simpa only [mul_comm] using this
  · intro hh
    have hl := Real.exp_le_exp.mpr hh.1
    have hu := Real.exp_le_exp.mpr hh.2
    rw [Real.exp_log (by norm_num),he] at hl
    rw [he,Real.exp_add,Real.exp_log (by norm_num)] at hu
    refine ⟨?_,?_⟩
    · have := (le_div_iff₀ hNr).mp hl
      exact_mod_cast this
    · have := (div_le_iff₀ hNr).mp hu
      nlinarith

/-- Length plus ONE for each closed strip: both endpoint weights are paid. -/
theorem actual_edge_count (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : 0 ≤ δ) :
    (((domain N).filter (fun n => Edge (Real.log 2) δ (position (N:ℝ) n))).card:ℝ)
      ≤ 3*(N:ℝ)*(Real.exp δ-1)+2 := by
  classical
  let s₀ := (domain N).filter (fun n => position (N:ℝ) n ∈ Set.Icc 0 δ)
  let s₁ := (domain N).filter (fun n => position (N:ℝ) n ∈ Set.Icc (Real.log 2) (Real.log 2+δ))
  have hE : (domain N).filter (fun n => Edge (Real.log 2) δ (position (N:ℝ) n)) = s₀ ∪ s₁ := by
    ext n
    simp [s₀,s₁,Edge,Finset.mem_union,Finset.mem_filter,and_or_left]
  have hExp : 1 ≤ Real.exp δ := Real.one_le_exp_iff.mpr hδ
  have h₀ := shifted_card_le s₀ N ((N:ℝ)*Real.exp δ)
    (by
      have hh := mul_le_mul_of_nonneg_left hExp (show (0:ℝ) ≤ (N:ℝ) from Nat.cast_nonneg N)
      simpa only [mul_one] using hh) (by
      intro n hn
      exact (edge_coordinate_bounds N n hN δ).1 (Finset.mem_filter.mp hn).2)
  have h₁ := shifted_card_le s₁ (2*N) (2*(N:ℝ)*Real.exp δ)
    (by
      have hh := mul_le_mul_of_nonneg_left hExp (show (0:ℝ) ≤ 2*(N:ℝ) by positivity)
      simpa only [mul_one,Nat.cast_mul,Nat.cast_ofNat] using hh) (by
      intro n hn
      exact (edge_coordinate_bounds N n hN δ).2 (Finset.mem_filter.mp hn).2)
  have hu : ((s₀ ∪ s₁).card:ℝ) ≤ (s₀.card:ℝ)+(s₁.card:ℝ) := by
    exact_mod_cast Finset.card_union_le s₀ s₁
  rw [hE]
  push_cast at h₁
  linarith

/-- Literal finite desmoothing, with a geometry-dependent bound and no cancellation. -/
theorem desmoothing_exp_bound (N : ℕ) (hN : 1 ≤ N) (δ t : ℝ)
    (hδ : 0 < δ) («hδλ» : δ ≤ Real.log 2) :
    ‖dyadic N t-smoothFinite (N:ℝ) δ t‖ ≤
      (3*(Real.exp δ-1)+2/(N:ℝ))*Real.log (4*(N:ℝ)) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog : 0 ≤ Real.log (4*(N:ℝ)) := Real.log_nonneg (by
    have hNr1 : (1:ℝ)≤N := by exact_mod_cast hN
    linarith)
  have hh := finite_desmoothing (domain N) (coefficient t) (position (N:ℝ))
    (Real.log 2) δ (Real.log (4*(N:ℝ))/(N:ℝ)) hδ «hδλ» (by positivity)
    (fun n hn => coefficient_bound N n hN t hn)
  rw [sharp_on_domain N hN t,smooth_on_domain N hN δ t hδ] at hh
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_right (actual_edge_count N hN δ hδ.le)
    (show 0≤Real.log (4*(N:ℝ))/(N:ℝ) by positivity)
  convert hb using 1 <;> field_simp <;> ring

/-- A convenient elementary exponential increment bound on [0,1/2]. -/
theorem exp_increment (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1/2) :
    Real.exp δ-1 ≤ 2*δ := by
  have hh := Real.abs_exp_sub_one_le (x:=δ)
    (by rw [abs_of_nonneg hδ]; linarith)
  simpa only [abs_of_nonneg hδ] using (le_abs_self (Real.exp δ-1)).trans hh

theorem log_two_ge_half : (1/2:ℝ) ≤ Real.log 2 := by
  have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<1/2)
  rw [one_div,Real.log_inv] at hh
  norm_num at hh
  linarith

/-- The parent's exact two-endpoint error is now instantiated for actual Λ weights. -/
theorem literal_desmoothing (N : ℕ) (hN : 1 ≤ N) (δ t : ℝ)
    (hlog : 2 ≤ Real.log (N:ℝ)) (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) :
    ‖dyadic N t-smoothFinite (N:ℝ) δ t‖ ≤
      12*δ*Real.log (N:ℝ)+4*Real.log (N:ℝ)/(N:ℝ) := by
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := log_two_ge_half
  have «hδλ» := hδ1.trans hlog2
  have hg := desmoothing_exp_bound N hN δ t hδ «hδλ»
  have hexp := exp_increment δ hδ.le hδ1
  have hlog4 : Real.log (4*(N:ℝ)) ≤ 2*Real.log (N:ℝ) := by
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) hNr.ne',
      show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢
    linarith
  have hl0 : 0 ≤ Real.log (4*(N:ℝ)) := Real.log_nonneg (by
    have : (1:ℝ)≤N := by exact_mod_cast hN
    linarith)
  have hcoef : 0 ≤ 6*δ+2/(N:ℝ) := by positivity
  apply hg.trans
  have hh := mul_le_mul (show 3*(Real.exp δ-1)+2/(N:ℝ)≤6*δ+2/(N:ℝ) by linarith)
    hlog4 hl0 hcoef
  convert hh using 1 <;> ring

end Item1SharpDyadicSmoothing

-- ROOT CAP RECURSIVE AUDIT: original declarations only.
run_cmd do
  for target in [
    ``Item1SharpDyadicSmoothing.coefficient_eq_term,
    ``Item1SharpDyadicSmoothing.domain_bounds,
    ``Item1SharpDyadicSmoothing.exp_position,
    ``Item1SharpDyadicSmoothing.sharp_membership,
    ``Item1SharpDyadicSmoothing.sharp_on_domain,
    ``Item1SharpDyadicSmoothing.smooth_on_domain,
    ``Item1SharpDyadicSmoothing.coefficient_norm,
    ``Item1SharpDyadicSmoothing.coefficient_bound,
    ``Item1SharpDyadicSmoothing.shifted_card_le,
    ``Item1SharpDyadicSmoothing.edge_coordinate_bounds,
    ``Item1SharpDyadicSmoothing.actual_edge_count,
    ``Item1SharpDyadicSmoothing.desmoothing_exp_bound,
    ``Item1SharpDyadicSmoothing.exp_increment,
    ``Item1SharpDyadicSmoothing.log_two_ge_half,
    ``Item1SharpDyadicSmoothing.literal_desmoothing] do
    for ax in (← Lean.collectAxioms target) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {target}"
  Lean.logInfo "Item1SharpDyadicSmoothing: 15 original theorem guards passed."
