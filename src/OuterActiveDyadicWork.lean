import OuterSmoothSupportGeometryWork
import Mathlib.Data.Nat.Log

/-! Retain only rectangular dyadic blocks meeting the nonzero smoothed
source. This retains product geometry before taking Fourier absolute values. -/
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace OuterActiveDyadicWork
open OuterSmoothSupportGeometryWork OuterSmoothErrorSupportWork OuterSourceReindexWork
open OuterSmoothCoreWork OuterSmoothStepWork OuterBufferedSourceWork LongerTupleEncoding

abbrev BlockKey := ℕ×ℕ×ℕ×ℕ
def blockKey (r : Representation) : BlockKey :=
  (r.1.log2,(drop r).1.log2,(drop r).2.1.log2,(drop r).2.2.log2)
def activeKeys (X s : ℝ) (i j : ℕ) : Finset BlockKey :=
  (activeSource X s i j).image blockKey
def localizedSource (X s : ℝ) (i j : ℕ) : Finset Representation :=
  (ambient X).filter (fun r => blockKey r ∈ activeKeys X s i j)

theorem localized_subset (X s : ℝ) (i j : ℕ) : localizedSource X s i j ⊆ ambient X :=
  Finset.filter_subset _ _

theorem active_subset_localized (X s : ℝ) (i j : ℕ) :
    activeSource X s i j ⊆ localizedSource X s i j := by
  intro r hr
  exact Finset.mem_filter.mpr ⟨(active_data X s i j r hr).1,Finset.mem_image.mpr ⟨r,hr,rfl⟩⟩

theorem localized_witness (X s : ℝ) (i j : ℕ) (r : Representation)
    (hr : r ∈ localizedSource X s i j) :
    ∃q∈activeSource X s i j,blockKey q=blockKey r := by
  exact Finset.mem_image.mp (Finset.mem_filter.mp hr).2

theorem smooth_coefficient_zero_off (X s : ℝ) (i j : ℕ) (r : Representation)
    (hr : r ∈ ambient X) (hout : r ∉ localizedSource X s i j) :
    atomMultiplier X s i j r*smoothCuts (width X) (Real.log (r.1:ℝ))
      (cutoffLogs X s (drop r) i j) = 0 := by
  by_contra hh
  exact hout (active_subset_localized X s i j (Finset.mem_filter.mpr ⟨hr,hh⟩))

theorem smoothBox_localized (X s L R : ℝ) (i j : ℕ) :
    smoothBox X s L R i j = ∑r∈localizedSource X s i j,
      atomMultiplier X s i j r*smoothCuts (width X) (Real.log (r.1:ℝ))
        (cutoffLogs X s (drop r) i j)*UpperAfter545Remaining.floorKernel L R (index r) := by
  symm
  apply Finset.sum_subset (localized_subset X s i j)
  intro r hr hout
  rw [smooth_coefficient_zero_off X s i j r hr hout,zero_mul]

theorem same_log2_ratio (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (he : m.log2=n.log2) :
    m < 2*n ∧ n < 2*m := by
  have hmL := Nat.log2_self_le (Nat.ne_of_gt hm)
  have hnL := Nat.log2_self_le (Nat.ne_of_gt hn)
  have hmU := Nat.lt_log2_self (n := m)
  have hnU := Nat.lt_log2_self (n := n)
  simp only [he,Nat.pow_succ] at hmU hmL
  rw [Nat.pow_succ] at hnU
  constructor <;> omega

theorem same_log2_log (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (he : m.log2=n.log2) :
    Real.log (m:ℝ) < Real.log (n:ℝ)+Real.log 2 ∧
      Real.log (n:ℝ) < Real.log (m:ℝ)+Real.log 2 := by
  have hh := same_log2_ratio m n hm hn he
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have h1 := Real.log_lt_log hmR (by exact_mod_cast hh.1 : (m:ℝ) < 2*n)
  have h2 := Real.log_lt_log hnR (by exact_mod_cast hh.2 : (n:ℝ) < 2*m)
  rw [Real.log_mul (by norm_num) hnR.ne'] at h1
  rw [Real.log_mul (by norm_num) hmR.ne'] at h2
  constructor <;> linarith

run_cmd do
  for decl in [``localized_subset, ``active_subset_localized, ``localized_witness,
      ``smooth_coefficient_zero_off, ``smoothBox_localized, ``same_log2_ratio, ``same_log2_log] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterActiveDyadicWork
