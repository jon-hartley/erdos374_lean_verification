import TailSieveCovered

/-! Long actual lower-source profiles automatically satisfy the previously
proved final-band cutoff. The fourth-coordinate cubic test suffices for
both signs; no analytic estimate or prime-distribution input is added. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
attribute [local instance] Classical.propDecidable

namespace FrontierProfileClassification
open SieveBoxGrouping SieveGeometricGrid

theorem last_index_le (g:List ℕ) (j:ℕ) (hg:(g++[j]).Pairwise (·≥·)) :
    ∀i∈g++[j],j ≤ i := by
  intro i hi
  rcases List.mem_append.mp hi with hi|hi
  · exact (List.pairwise_append.mp hg).2.2 i hi j (by simp)
  · have he : i=j := by simpa using hi
    exact he.ge

theorem sixth_power_lt (B c:ℝ) (xs:List ℝ) (hc:0<c)
    (hxs:∀x∈xs,c≤x) (hlen:3<xs.length)
    (ht:(xs.take 3).prod*xs[3]^3<B) : c^6<B := by
  have hp : c^3≤(xs.take 3).prod := by
    have hh := SieveBoxLength.rpow_length_le_prod c 1 (xs.take 3) hc
      (fun x hx => by simpa only [Real.rpow_one] using hxs x (List.mem_of_mem_take hx))
    simpa only [List.length_take,Nat.min_eq_left (by omega : 3≤xs.length),
      Nat.cast_ofNat,mul_one,Real.rpow_ofNat] using hh
  have hlast : c≤xs[3] := hxs _ (List.getElem_mem hlen)
  have hp0 : 0≤(xs.take 3).prod := (pow_nonneg hc.le 3).trans hp
  have hh := mul_le_mul hp (pow_le_pow_left₀ hc.le hlast 3) (pow_nonneg hc.le 3) hp0
  have he : c^3*c^3=c^6 := by ring
  rw [he] at hh
  exact hh.trans_lt ht

theorem last_sixth_lt_level (positive:Bool) (D s:ℝ) (hD:1<D) (hs:0<s)
    (g:List ℕ) (j:ℕ) (hg:g++[j]∈profiles positive D s)
    (hlen:4≤(g++[j]).length) : (scale D s j)^6<D := by
  have htest := ((mem_profiles positive D s (g++[j])).mp hg).2.2
  have hpair : (g++[j]).Pairwise (·≥·) := by
    cases positive
    · exact htest.2.1
    · exact htest.2.1.imp (fun h => h.le)
  let xs := (g++[j]).map (scale D s)
  have hxs : ∀x∈xs,scale D s j≤x := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    exact (scale_strictMono D s hD hs).monotone (last_index_le g j hpair i hi)
  have hc : 0<scale D s j := Real.rpow_pos_of_pos (by linarith) _
  have hlen' : 3<xs.length := by simp only [xs,List.length_map]; omega
  apply sixth_power_lt D (scale D s j) xs hc hxs hlen'
  cases positive
  · have hh := (SieveBoxPrefix.accepts_iff_prefix_tests D false 1 xs).mp htest.2.2
      3 hlen' (by decide)
    simpa only [one_mul] using hh
  · have hh := (SieveBoxPrefix.accepts_iff_prefix_tests (D^(1/ratio s)) false 1 xs).mp htest.2.2
      3 hlen' (by decide)
    have hcut := FourPrimeSmallWeights.inner_cutoff_le D s hD.le hs.le
    have hh' : (xs.take 3).prod*xs[3]^3<D^(1/ratio s) := by
      simpa only [one_mul] using hh
    exact hh'.trans_le hcut

theorem ratio_level_exponent_le (s:ℝ) (hs:0≤s) (hs1:s≤1/3) :
    (1-3*s)*ratio s≤1 := by
  have h9 : s^9≤s := by
    simpa only [pow_one] using pow_le_pow_of_le_one hs (show s≤1 by linarith) (by decide : 1≤9)
  have hh := mul_le_mul_of_nonneg_left h9 (show 0≤1-3*s by linarith)
  unfold ratio
  nlinarith [sq_nonneg s]

theorem last_band_lt_of_length_ge_four (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (positive:Bool) (g:List ℕ) (j:ℕ)
    (hg:g++[j]∈profiles positive (SieveWeightedCutoffs.level X s) s)
    (hlen:4≤(g++[j]).length) :
    scale (SieveWeightedCutoffs.level X s) s (j+1)<X^(1/6:ℝ) := by
  let D := SieveWeightedCutoffs.level X s
  have hD : 1<D := Real.one_lt_rpow hX (by linarith)
  have hDp : 0<D := by linarith
  have hc : 0<scale D s j := Real.rpow_pos_of_pos hDp _
  have hr : 0<ratio s := (one_lt_ratio s hs).trans' zero_lt_one
  have hh := last_sixth_lt_level positive D s hD hs g j hg hlen
  have hroot := Real.rpow_lt_rpow (pow_nonneg hc.le 6) hh (by norm_num : (0:ℝ)<1/6)
  have hroot' : scale D s j<D^(1/6:ℝ) := by
    simpa only [←Real.rpow_natCast_mul hc.le,Nat.cast_ofNat,show (6:ℝ)*(1/6)=1 by norm_num,
      Real.rpow_one] using hroot
  rw [scale_succ _ _ hDp.le]
  refine (Real.rpow_lt_rpow hc.le hroot' hr).trans_le ?_
  rw [←Real.rpow_mul hDp.le]
  dsimp [D,SieveWeightedCutoffs.level]
  rw [←Real.rpow_mul (show 0≤X by linarith)]
  apply Real.rpow_le_rpow_of_exponent_le hX.le
  have he := ratio_level_exponent_le s hs.le (by linarith)
  nlinarith

theorem inner_last_band_le (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (g:List ℕ) (j:ℕ)
    (hg:g++[j]∈profiles true (SieveWeightedCutoffs.level X s) s)
    (hlen:4≤(g++[j]).length) :
    scale (SieveWeightedCutoffs.level X s) s (j+1)≤X^(1/6:ℝ) :=
  (last_band_lt_of_length_ge_four X s hX hs hs1 true g j hg hlen).le

theorem outer_last_band_le (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (g:List ℕ) (j:ℕ)
    (hg:g++[j]∈profiles false (SieveWeightedCutoffs.level X s) s)
    (hlen:5≤(g++[j]).length) :
    scale (SieveWeightedCutoffs.level X s) s (j+1)≤X^(1/6:ℝ) :=
  (last_band_lt_of_length_ge_four X s hX hs hs1 false g j hg (by omega)).le

theorem long_profile_mem_covered (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (positive:Bool) (g:List ℕ) (j:ℕ)
    (hg:g++[j]∈profiles positive (SieveWeightedCutoffs.level X s) s)
    (hlen:4≤(g++[j]).length) :
    (positive,(g,j))∈TailSieveCovered.family X s := by
  have hp := (mem_profiles positive _ s (g++[j])).mp hg
  have hglen : g.length≤SieveBoxLength.cutoff s := by
    have hh := hp.1
    simp only [List.length_append,List.length_singleton] at hh
    omega
  have hgnil : g≠[] := by intro he; simp only [he,List.nil_append,List.length_singleton] at hlen; omega
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    refine ⟨Finset.mem_univ _,Finset.mem_product.mpr ⟨?_,?_⟩⟩
    · apply (SieveBoxedFamily.mem_boundedTuples _ _ _).mpr
      refine ⟨hglen,?_⟩
      intro i hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hp.2.1 i (List.mem_append_left _ hi)))
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hp.2.1 j (by simp)))
  · exact ⟨hgnil,hg,(last_band_lt_of_length_ge_four X s hX hs hs1 positive g j hg hlen).le⟩

theorem covered_representation_of_length_ge_four (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (positive:Bool) (h:List ℕ)
    (hh:h∈profiles positive (SieveWeightedCutoffs.level X s) s) (hlen:4≤h.length) :
    ∃g:List ℕ, ∃j:ℕ, h=g++[j] ∧ (positive,(g,j))∈TailSieveCovered.family X s := by
  have hne : h≠[] := by intro he; simp only [he,List.length_nil] at hlen; omega
  have he := List.dropLast_append_getLast hne
  refine ⟨h.dropLast,h.getLast hne,he.symm,?_⟩
  apply long_profile_mem_covered X s hX hs hs1 positive _ _
  · simpa only [he] using hh
  · simpa only [he] using hlen

theorem large_last_band_length_lt_four (X s:ℝ) (hX:1<X) (hs:0<s) (hs1:s≤1/1000)
    (positive:Bool) (g:List ℕ) (j:ℕ)
    (hg:g++[j]∈profiles positive (SieveWeightedCutoffs.level X s) s)
    (hband:X^(1/6:ℝ)≤scale (SieveWeightedCutoffs.level X s) s (j+1)) :
    (g++[j]).length<4 := by
  apply Nat.lt_of_not_ge
  intro hlen
  exact (last_band_lt_of_length_ge_four X s hX hs hs1 positive g j hg hlen).not_ge hband

run_cmd do
  for decl in [``last_index_le,``sixth_power_lt,``last_sixth_lt_level,
      ``ratio_level_exponent_le,``last_band_lt_of_length_ge_four,
      ``inner_last_band_le,``outer_last_band_le,``long_profile_mem_covered,
      ``covered_representation_of_length_ge_four,``large_last_band_length_lt_four] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL LONG LOWER PROFILES BELONG TO CHECKED 1/6 COVERED CLASS"

end FrontierProfileClassification
