import SourceFractionalGeometryStrong
import SourceMomentQuantization

/-! v6: actual finite rational moment choices and the rounding/length bridge.
UNCOMPILED DRAFT. The strong certificate is an uncompiled prerequisite. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace SourceSelectedOrders
open SourceFractionalGeometryStrong SourceMomentQuantization

def convolutionOrder (i : Fin 8) : ℕ :=
  match i.val with
  | 0 => 5 | 1 => 5 | 2 => 4 | 3 => 4
  | 4 => 3 | 5 => 3 | 6 => 2 | _ => 2

def rawOrder (i : Fin 8) (x : ℝ) : ℝ :=
  match i.val with
  | 0 => 4*nuPlus/x-10 | 1 => 10
  | 2 => 4*nuPlus/x-8 | 3 => 8
  | 4 => 4*nuPlus/x-6 | 5 => 6
  | 6 => 4*nuPlus/x-4 | _ => 4

theorem convolutionOrder_bounds (i : Fin 8) :
    2 ≤ convolutionOrder i ∧ convolutionOrder i ≤ 5 := by
  fin_cases i <;> norm_num [convolutionOrder]

/-- Algebra of the nonconstant branches, with denominators made explicit. -/
theorem variable_order_data (h x : ℝ) (hh : 0 < h) (hx : 0 < x)
    (hlo : 4*h*x ≤ 4*nuPlus) (hhi : 4*nuPlus ≤ (4*h+2)*x) :
    2*h ≤ 4*nuPlus/x-2*h ∧ 4*nuPlus/x-2*h ≤ 2*h+2 ∧
    4*nuPlus ≤ x*((4*nuPlus/x-2*h)+2*h) ∧
    2/(4*nuPlus/x-2*h) = frac h x := by
  have hl : 4*h ≤ 4*nuPlus/x := (le_div_iff₀ hx).mpr hlo
  have hu : 4*nuPlus/x ≤ 4*h+2 := (div_le_iff₀ hx).mpr hhi
  have hb : 0 < 4*nuPlus/x-2*h := by linarith
  have hprod : 0 < h*x := mul_pos hh hx
  have hd : 0 < 4*nuPlus-2*h*x := by nlinarith
  refine ⟨by linarith,by linarith,?_,?_⟩
  · have he : x*((4*nuPlus/x-2*h)+2*h) = 4*nuPlus := by field_simp <;> ring
    exact he.ge
  · unfold frac
    field_simp [hx.ne',hb.ne',hd.ne']
    <;> ring

theorem band_data (i : Fin 8) (x : ℝ) (hx : band i x) :
    1/6 ≤ x ∧ x ≤ 1/2 ∧
    2*(convolutionOrder i:ℝ) ≤ rawOrder i x ∧
    rawOrder i x ≤ 2*(convolutionOrder i:ℝ)+2 ∧
    4*nuPlus ≤ x*(rawOrder i x+2*(convolutionOrder i:ℝ)) ∧
    2/rawOrder i x = reciprocal i x := by
  fin_cases i
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    have hv := variable_order_data 5 x (by norm_num) hxp
      (by norm_num [nuPlus] at *; nlinarith)
      (by norm_num [nuPlus] at *; nlinarith)
    convert hv using 1 <;> norm_num [convolutionOrder,rawOrder,reciprocal]
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    norm_num [convolutionOrder,rawOrder,reciprocal,nuPlus] at *
    nlinarith
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    have hv := variable_order_data 4 x (by norm_num) hxp
      (by norm_num [nuPlus] at *; nlinarith)
      (by norm_num [nuPlus] at *; nlinarith)
    convert hv using 1 <;> norm_num [convolutionOrder,rawOrder,reciprocal]
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    norm_num [convolutionOrder,rawOrder,reciprocal,nuPlus] at *
    nlinarith
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    have hv := variable_order_data 3 x (by norm_num) hxp
      (by norm_num [nuPlus] at *; nlinarith)
      (by norm_num [nuPlus] at *; nlinarith)
    convert hv using 1 <;> norm_num [convolutionOrder,rawOrder,reciprocal]
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    norm_num [convolutionOrder,rawOrder,reciprocal,nuPlus] at *
    nlinarith
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    have hv := variable_order_data 2 x (by norm_num) hxp
      (by norm_num [nuPlus] at *; nlinarith)
      (by norm_num [nuPlus] at *; nlinarith)
    convert hv using 1 <;> norm_num [convolutionOrder,rawOrder,reciprocal]
  · simp only [band] at hx
    rcases hx with ⟨hlo,hhi⟩
    have hxp : 0 < x := by norm_num at hlo hhi; linarith
    refine ⟨by norm_num at hlo hhi; linarith,
      by norm_num at hlo hhi; linarith,?_⟩
    norm_num [convolutionOrder,rawOrder,reciprocal,nuPlus] at *
    nlinarith

/-- A pair of length exponents produces literal rational orders, not just a
statement about their reciprocal sum. At most 8004 individual order tags occur. -/
theorem choose (u v : ℝ) (ht : Triangle u v) :
    ∃ h : Fin 3 → ℕ, ∃ β : Fin 3 → ℝ,
      (∀ i, 2 ≤ h i ∧ h i ≤ 5 ∧ 2*(h i:ℝ) ≤ β i ∧ β i ≤ 2*(h i:ℝ)+2) ∧
      (∀ i, 4*nuPlus ≤ (![u,v,1-u-v] i)*(β i+2*(h i:ℝ))) ∧
      (2001/2000:ℝ) ≤ 2/β 0+2/β 1+2/β 2 := by
  obtain ⟨i,j,k,hi,hj,hk,hS⟩ := triangle_surplus u v ht
  have di := band_data i u hi
  have dj := band_data j v hj
  have dk := band_data k (1-u-v) hk
  let hs : Fin 3 → ℕ := ![convolutionOrder i,convolutionOrder j,convolutionOrder k]
  let b : Fin 3 → ℝ := ![rawOrder i u,rawOrder j v,rawOrder k (1-u-v)]
  let β : Fin 3 → ℝ := fun l => rounded (b l)
  have hdata (l : Fin 3) : 2 ≤ hs l ∧ hs l ≤ 5 ∧
      2*(hs l:ℝ) ≤ b l ∧ b l ≤ 2*(hs l:ℝ)+2 ∧
      4*nuPlus ≤ (![u,v,1-u-v] l)*(b l+2*(hs l:ℝ)) := by
    fin_cases l
    · exact ⟨(convolutionOrder_bounds i).1,(convolutionOrder_bounds i).2,
        di.2.2.1,di.2.2.2.1,di.2.2.2.2.1⟩
    · exact ⟨(convolutionOrder_bounds j).1,(convolutionOrder_bounds j).2,
        dj.2.2.1,dj.2.2.2.1,dj.2.2.2.2.1⟩
    · exact ⟨(convolutionOrder_bounds k).1,(convolutionOrder_bounds k).2,
        dk.2.2.1,dk.2.2.2.1,dk.2.2.2.2.1⟩
  have hb4 (l : Fin 3) : 4 ≤ b l := by
    have hh : (2:ℝ) ≤ hs l := by exact_mod_cast (hdata l).1
    linarith [(hdata l).2.2.1]
  refine ⟨hs,β,?_,?_,?_⟩
  · intro l
    have hh := finite_order (hs l) (b l) (hdata l).1 (hdata l).2.2.1 (hdata l).2.2.2.1
    exact ⟨(hdata l).1,(hdata l).2.1,hh.2.2.1,hh.2.2.2⟩
  · intro l
    apply length_guard_preserved _ _ _ _ _ (by linarith [hb4 l]) (hdata l).2.2.2.2
    fin_cases l <;> dsimp <;> linarith [di.1,dj.1,dk.1]
  · apply required_surplus (b 0) (b 1) (b 2) (hb4 0) (hb4 1) (hb4 2)
    change (1001/1000:ℝ) ≤ 2/rawOrder i u+2/rawOrder j v+2/rawOrder k (1-u-v)
    rw [di.2.2.2.2.2,dj.2.2.2.2.2,dk.2.2.2.2.2]
    exact hS

/-- Fixed interval and floor losses are absorbed with an explicit, loose
logarithmic threshold. No numerical effective prime theorem is implied. -/
theorem physical_length_guard (X x β : ℝ) (D h : ℕ)
    (hX : 2 ≤ X) (hlog : 1000000 ≤ Real.log X) (hD : 1 ≤ D)
    (hDx : X^x/16 ≤ (D:ℝ)) (hh : 2 ≤ h) (hh5 : h ≤ 5)
    (hβ0 : 2*(h:ℝ) ≤ β) (hβ1 : β ≤ 2*(h:ℝ)+2)
    (hguard : 4*nuPlus ≤ x*(β+2*(h:ℝ))) :
    (2*X^(562/625:ℝ))^4 ≤ (D:ℝ)^(β+2*(h:ℝ)) := by
  have hXp : 0 < X := by linarith
  have hDp : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hhr : (2:ℝ) ≤ h := by exact_mod_cast hh
  have hhr5 : (h:ℝ) ≤ 5 := by exact_mod_cast hh5
  have hA0 : 0 ≤ β+2*(h:ℝ) := by linarith
  have hA25 : β+2*(h:ℝ) ≤ 25 := by linarith
  have hl2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  have hl16 : Real.log 16 = 4*Real.log 2 := by
    rw [show (16:ℝ) = 2^4 by norm_num,Real.log_pow]
    norm_num
  have hdl := Real.log_le_log (by positivity : (0:ℝ) < X^x/16) hDx
  rw [Real.log_div (Real.rpow_pos_of_pos hXp _).ne' (by norm_num),
    Real.log_rpow hXp,hl16] at hdl
  have hg := mul_le_mul_of_nonneg_right hguard (by linarith : 0 ≤ Real.log X)
  have hdg := mul_le_mul_of_nonneg_left hdl hA0
  have hconst := mul_le_mul_of_nonneg_left hA25
    (show 0 ≤ 4*Real.log 2 by positivity)
  apply (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hDp _)).mp
  rw [Real.log_pow,Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hXp _).ne',
    Real.log_rpow hXp,Real.log_rpow hDp]
  norm_num [nuPlus] at hg ⊢
  nlinarith

#print axioms choose
run_cmd do
  for n in [``convolutionOrder_bounds,``variable_order_data,``band_data,``choose,``physical_length_guard] do
    for ax in (← Lean.collectAxioms n) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {n}"
  Lean.logInfo "SOURCE SELECTED ORDERS: VALID ONLY AFTER SUCCESSFUL COMPILATION"
end SourceSelectedOrders
