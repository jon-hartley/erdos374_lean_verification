import LongPairHighCoreMeanWork

/-! Sharper literal upper geometry after removing the selected-prime edge.
The small divisor and the remaining core restrictions are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace LongPairHighCoreGeometryWork
open SieveWeightedCutoffs SieveBoxedFamily LongerTupleSector
open LongerTupleActualProfiles PositiveSharpBoxedCount
open LongPairHighCoreMeanWork ShortPairSplitWork

theorem physical_pair_lt (X s g : ℝ) (p d a b : ℕ)
    (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000) (hp : 0<p)
    (hD : 1<level X s/p)
    (hd : d∈SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (ht : [a,b]∈SieveUpperBoxing.outerFamily (level X s/p) s (cutoffThree X s p))
    (hselected : X^g<(b:ℝ)) :
    ((p*d*a*b:ℕ):ℝ)<X^((1-g)*(1-3*s):ℝ) := by
  have hX0 : 0<X := by linarith
  have hp0 : (0:ℝ)<p := by exact_mod_cast hp
  have hd0 : (0:ℝ)<d := by exact_mod_cast UpperAfter545Geometry.smallCarrier_pos _ _ _ hd
  have hpool := (LongerTupleGeometry.family_data _ s _ hD hs [a,b] (Or.inl ht)).1
  have ha := (mem_pool _ s _ a).mp (hpool a (by simp))
  have hb := (mem_pool _ s _ b).mp (hpool b (by simp))
  have ha0 : (0:ℝ)<a := by exact_mod_cast ha.1.pos
  have hb0 : (0:ℝ)<b := by exact_mod_cast hb.1.pos
  have hqa := Real.log_lt_log ha0 ha.2.1
  have hqb := Real.log_lt_log hb0 hb.2.1
  rw [log_three X s p hX0 hp0] at hqa hqb
  have halong := Real.log_lt_log (Real.rpow_pos_of_pos hX0 g) hselected
  rw [Real.log_rpow hX0] at halong
  have hpLog : Real.log (p:ℝ)<(1-3*s-3*g)*Real.log X := by linarith
  have hds := PositiveSharpRemainderSupportGeometry.smallCarrier_lt _ s hD hs
    (by linarith) d hd
  have hdl := Real.log_lt_log hd0 hds
  rw [Real.log_rpow (by linarith : 0<level X s/p)] at hdl
  have hDlog : Real.log (level X s/p) = (1-3*s)*Real.log X-Real.log (p:ℝ) := by
    rw [level,Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hp0.ne',Real.log_rpow hX0]
  rw [hDlog] at hdl
  have hpTerm := mul_lt_mul_of_pos_left hpLog (by linarith : 0<(1/3:ℝ)-s)
  have hsum : Real.log (p:ℝ)+Real.log (d:ℝ)+Real.log (a:ℝ)+Real.log (b:ℝ) <
      ((1-g)*(1-3*s))*Real.log X := by
    calc
      _ < Real.log (p:ℝ)+(s+2/3)*((1-3*s)*Real.log X-Real.log (p:ℝ)) := by linarith
      _ = (s+2/3)*(1-3*s)*Real.log X+(1/3-s)*Real.log (p:ℝ) := by ring
      _ < (s+2/3)*(1-3*s)*Real.log X+(1/3-s)*((1-3*s-3*g)*Real.log X) :=
        add_lt_add_of_le_of_lt le_rfl hpTerm
      _ = _ := by ring
  have hprod0 : (0:ℝ)<((p*d*a*b:ℕ):ℝ) := by
    simpa only [Nat.cast_mul] using mul_pos (mul_pos (mul_pos hp0 hd0) ha0) hb0
  apply (Real.log_lt_log_iff hprod0
    (Real.rpow_pos_of_pos hX0 _)).mp
  simpa only [Nat.cast_mul,Real.log_mul (mul_pos (mul_pos hp0 hd0) ha0).ne' hb0.ne',
    Real.log_mul (mul_pos hp0 hd0).ne' ha0.ne',Real.log_mul hp0.ne' hd0.ne',
    Real.log_rpow hX0] using hsum

theorem core_source_upper (X s : ℝ) (hX : 1<X) (hs : 0<s) (hs1 : s≤1/1000)
    (hlog : 1000≤Real.log X) (r : LongerTupleEncoding.Representation)
    (hr : r∈highCoreSource X s) :
    (LongerTupleEncoding.index r:ℝ)<X^((771/1000:ℝ)*(1-3*s)) := by
  obtain ⟨hr,hselected⟩ := Finset.mem_filter.mp hr
  have hrcol := (Finset.mem_filter.mp hr).1
  obtain ⟨hp,hd,ht,hlen,_,_⟩ := (LongPairCollectionWork.mem_source X s _ _ r).mp hrcol
  obtain ⟨a,b,he⟩ := List.length_eq_two.mp hlen
  have hg := large_band_geometry X s hX hs hs1 hlog r.1 hp
  have hb : X^(229/1000:ℝ)<(b:ℝ) := by
    simpa only [ShortPairSplitWork.prime,he,ite_true,List.getD_cons_zero,
      List.getD_cons_succ] using hselected
  have hh := physical_pair_lt X s (229/1000) r.1 r.2.1 a b hX hs hs1 (by omega)
    hg.2.2.1 hd (by simpa only [he] using ht) hb
  norm_num at hh
  simpa [LongerTupleEncoding.index,he,mul_assoc] using hh

#print axioms core_source_upper
run_cmd do
  for decl in [``physical_pair_lt, ``core_source_upper] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"

end LongPairHighCoreGeometryWork
