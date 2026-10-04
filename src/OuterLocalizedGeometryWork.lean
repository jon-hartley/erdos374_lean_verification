import OuterActiveDyadicWork

/-! Product and cofactor geometry survives throughout every selected
rectangular dyadic block, including the Fourier-mode extension within it. -/
set_option autoImplicit false
noncomputable section
namespace OuterLocalizedGeometryWork
open OuterActiveDyadicWork OuterSmoothSupportGeometryWork OuterSmoothErrorSupportWork
open OuterSourceReindexWork LongerTupleEncoding

theorem ambient_log_index (X : ℝ) (hX : 2 ≤ X) (r : Representation) (hr : r ∈ ambient X) :
    Real.log (index r:ℝ) = Real.log (r.1:ℝ)+Real.log ((drop r).1:ℝ)+
      Real.log ((drop r).2.1:ℝ)+Real.log ((drop r).2.2:ℝ) := by
  have hd := ambient_data X hX r hr
  conv_lhs => rw [← rebuild_drop r hd.1]
  exact OuterPairLogConstraintsWork.log_index _ _ _ _ hd.2.2.1 hd.2.2.2.2.1
    hd.2.2.2.2.2.1 hd.2.2.2.2.2.2

theorem same_block_logs (X : ℝ) (hX : 2 ≤ X) (r q : Representation)
    (hr : r ∈ ambient X) (hq : q ∈ ambient X) (he : blockKey r=blockKey q) :
    Real.log (r.1:ℝ) < Real.log (q.1:ℝ)+Real.log 2 ∧
      Real.log (index r:ℝ) < Real.log (index q:ℝ)+4*Real.log 2 ∧
      Real.log (index q:ℝ) < Real.log (index r:ℝ)+4*Real.log 2 := by
  have hd := ambient_data X hX r hr
  have hd' := ambient_data X hX q hq
  simp only [blockKey,Prod.mk.injEq] at he
  have h0 := same_log2_log r.1 q.1 hd.2.2.1 hd'.2.2.1 he.1
  have h1 := same_log2_log (drop r).1 (drop q).1 hd.2.2.2.2.1 hd'.2.2.2.2.1 he.2.1
  have h2 := same_log2_log (drop r).2.1 (drop q).2.1 hd.2.2.2.2.2.1 hd'.2.2.2.2.2.1 he.2.2.1
  have h3 := same_log2_log (drop r).2.2 (drop q).2.2 hd.2.2.2.2.2.2 hd'.2.2.2.2.2.2 he.2.2.2
  rw [ambient_log_index X hX r hr,ambient_log_index X hX q hq]
  exact ⟨h0.1,by linarith,by linarith⟩

theorem localized_log_geometry (X s : ℝ) (hX : 2 ≤ X) (hs : 0 ≤ s)
    (i j : ℕ) (r : Representation) (hr : r ∈ localizedSource X s i j) :
    Real.log (r.1:ℝ) < (313/1000:ℝ)*Real.log X+width X+Real.log 2 ∧
    (26/35:ℝ)*Real.log X-width X-4*Real.log 2 < Real.log (index r:ℝ) ∧
    Real.log (index r:ℝ) < (193/250:ℝ)*Real.log X+width X+4*Real.log 2 := by
  obtain ⟨q,hq,he⟩ := localized_witness X s i j r hr
  have hg := active_log_geometry X s hX hs i j q hq
  have hh := same_block_logs X hX r q (localized_subset X s i j hr)
    (active_data X s i j q hq).1 he.symm
  exact ⟨by linarith,by linarith,by linarith⟩

theorem completed_cofactor_logs (X s : ℝ) (hX : 2 ≤ X) (hs : 0 ≤ s)
    (i j : ℕ) (r : Representation) (hr : r ∈ localizedSource X s i j)
    (k : ℕ) (hk : 0 < k) (hlo : X ≤ (index r:ℝ)*k) (hhi : (index r:ℝ)*k ≤ 2*X) :
    (57/250:ℝ)*Real.log X-width X-4*Real.log 2 < Real.log (k:ℝ) ∧
    Real.log (k:ℝ) < (9/35:ℝ)*Real.log X+width X+5*Real.log 2 := by
  have hg := localized_log_geometry X s hX hs i j r hr
  have hm : (0:ℝ) < index r := by
    exact_mod_cast OuterAmbientSizeWork.ambient_index_pos X hX r (localized_subset X s i j hr)
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hx : 0 < X := by linarith
  have h1 := Real.log_le_log hx hlo
  have h2 := Real.log_le_log (mul_pos hm hkR) hhi
  rw [Real.log_mul hm.ne' hkR.ne'] at h1 h2
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hx.ne'] at h2
  constructor <;> linarith

run_cmd do
  for decl in [``ambient_log_index, ``same_block_logs, ``localized_log_geometry,
      ``completed_cofactor_logs] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
end OuterLocalizedGeometryWork
