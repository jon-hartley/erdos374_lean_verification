import SieveUpperBoxWindow

/-! Product support bounds for the actual boxed families, obtained from
their real cubic tests and ordered box coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace PositiveSharpRemainderSupportGeometry
open SieveBoxedFamily

theorem cubic_dominates_pair (p q : ℝ) (hp : 1≤p) (hq : q≤p) : p*q≤p^3 := by
  have hpp : p*p≤p^3 := by
    nlinarith [mul_nonneg (sq_nonneg p) (show 0≤p-1 by linarith)]
  exact (mul_le_mul_of_nonneg_left hq (by linarith)).trans hpp

theorem lower_product_lt (D d : ℝ) (xs : List ℝ) (hd0 : 0≤d)
    (horder : xs.Pairwise (fun p q => q≤p)) (hpos : ∀p∈xs, 1≤p)
    (hd : d<D) (hroom : ∀p∈xs, d*p<D)
    (ha : SieveBoxPrefix.accepts D false d xs) : d*xs.prod<D := by
  induction xs using List.twoStepInduction generalizing d with
  | nil => simpa using hd
  | singleton p => simpa using hroom p (by simp)
  | cons_cons p q xs ih _ =>
      have hp : 1≤p := hpos p (by simp)
      have hq : 1≤q := hpos q (by simp)
      have hg : d*p*q^3<D := ha.2.1.resolve_left (by decide)
      have hqp : q≤q^3 := le_self_pow₀ hq (by decide)
      have hdp : 0≤d*p := mul_nonneg hd0 (by linarith)
      have hnew : d*p*q<D := (mul_le_mul_of_nonneg_left hqp hdp).trans_lt hg
      have htail := List.pairwise_cons.mp (List.pairwise_cons.mp horder).2
      have hroom' : ∀r∈xs, (d*p*q)*r<D := by
        intro r hr
        have hh := mul_le_mul_of_nonneg_left
          (cubic_dominates_pair q r hq (htail.1 r hr)) hdp
        have hh' : (d*p*q)*r≤d*p*q^3 := by simpa only [mul_assoc] using hh
        exact hh'.trans_lt hg
      have hh := ih (d*p*q) (mul_nonneg hdp (by linarith)) htail.2
        (fun r hr => hpos r (by simp [hr])) hnew hroom' ha.2.2
      simpa only [List.prod_cons, mul_assoc] using hh

theorem upper_product_lt (D d : ℝ) (xs : List ℝ) (hd0 : 0≤d)
    (horder : xs.Pairwise (fun p q => q≤p)) (hpos : ∀p∈xs, 1≤p)
    (hd : d<D) (ha : SieveBoxPrefix.accepts D true d xs) : d*xs.prod<D := by
  cases xs with
  | nil => simpa using hd
  | cons p xs =>
      have hp : 1≤p := hpos p (by simp)
      have hg : d*p^3<D := ha.1.resolve_left (by decide)
      have hpp : p≤p^3 := le_self_pow₀ hp (by decide)
      have hnew : d*p<D := (mul_le_mul_of_nonneg_left hpp hd0).trans_lt hg
      obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp horder
      have hroom : ∀q∈xs, (d*p)*q<D := by
        intro q hq
        have hh := mul_le_mul_of_nonneg_left (cubic_dominates_pair p q hp (hhead q hq)) hd0
        have hh' : (d*p)*q≤d*p^3 := by simpa only [mul_assoc] using hh
        exact hh'.trans_lt hg
      have hh := lower_product_lt D (d*p) xs (mul_nonneg hd0 (by linarith)) htail
        (fun q hq => hpos q (by simp [hq])) hnew hroom ha.2
      simpa only [List.prod_cons, mul_assoc] using hh

theorem scales_order (D s : ℝ) (hD : 1<D) (hs : 0<s) (t : List ℕ)
    (hi : (indices D s t).Pairwise (· ≥ ·)) :
    (scales D s t).Pairwise (fun p q => q≤p) := by
  rw [indices, List.pairwise_map] at hi
  rw [scales, List.pairwise_map]
  exact hi.imp (fun h => (SieveGeometricGrid.scale_strictMono D s hD hs).monotone h)

theorem prod_le_power (t : List ℕ) (f : ℕ→ℝ) (q : ℝ)
    (hf : ∀p∈t, 0≤f p) (hp : ∀p∈t, (p:ℝ)≤(f p)^q) :
    (t.prod:ℝ)≤((t.map f).prod)^q := by
  induction t with
  | nil => simp
  | cons p t ih =>
      have hf0 := hf p (by simp)
      have ht0 : 0≤(t.map f).prod := List.prod_nonneg (by
        intro x hx; obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx; exact hf a (by simp [ha]))
      simp only [List.prod_cons, Nat.cast_mul, List.map_cons]
      rw [Real.mul_rpow hf0 ht0]
      exact mul_le_mul (hp p (by simp))
        (ih (fun a ha => hf a (by simp [ha])) (fun a ha => hp a (by simp [ha])))
        (Nat.cast_nonneg _) (Real.rpow_nonneg hf0 _)

theorem boxed_tuple_product_le (D s z : ℝ) (hD : 1<D) (hs : 0<s) (hz : z≤D)
    (t : List ℕ) (mode : Bool) (hp : ∀p∈t, p∈pool D s z)
    (hi : (indices D s t).Pairwise (· ≥ ·))
    (ha : SieveBoxPrefix.accepts D mode 1 (scales D s t)) :
    (t.prod:ℝ)≤D^(SieveGeometricGrid.ratio s) := by
  have hpos : ∀x∈scales D s t, 1≤x := by
    intro x hx
    obtain ⟨p,_hp,rfl⟩ := List.mem_map.mp hx
    exact (Real.one_le_rpow hD.le (sq_nonneg s)).trans
      (SieveCompleteBoxing.coordinate_ge_initial D s hD hs p)
  have hroom : ∀x∈scales D s t, 1*x<D := by
    intro x hx
    obtain ⟨p,hpt,rfl⟩ := List.mem_map.mp hx
    have hc := coordinate_bounds D s z hD hs hz p (hp p hpt)
    simpa only [one_mul] using hc.2.1.trans_lt (((mem_pool D s z p).mp (hp p hpt)).2.1.trans_le hz)
  have hprod : (scales D s t).prod<D := by
    cases mode with
    | false =>
        simpa only [one_mul] using lower_product_lt D 1 _ zero_le_one
          (scales_order D s hD hs t hi) hpos hD hroom ha
    | true =>
        simpa only [one_mul] using upper_product_lt D 1 _ zero_le_one
          (scales_order D s hD hs t hi) hpos hD ha
  have hprod0 : 0≤(scales D s t).prod := List.prod_nonneg (fun x hx => (hpos x hx).trans' zero_le_one)
  have hb := prod_le_power t (coordinate D s) (SieveGeometricGrid.ratio s)
    (fun p ht => (coordinate_bounds D s z hD hs hz p (hp p ht)).1)
    (fun p ht => (coordinate_bounds D s z hD hs hz p (hp p ht)).2.2.le)
  exact hb.trans (Real.rpow_le_rpow hprod0 hprod.le
    (zero_le_one.trans (SieveGeometricGrid.one_lt_ratio s hs).le))

theorem lower_tuple_product_le (D s z : ℝ) (hD : 1<D) (hs : 0<s) (hz : z≤D)
    (t : List ℕ) (ht : t∈SieveCompleteBoxing.innerFamily D s z ∪
      SieveCompleteBoxing.outerFamily D s z) : (t.prod:ℝ)≤D^(SieveGeometricGrid.ratio s) := by
  rcases Finset.mem_union.mp ht with hi | ho
  · obtain ⟨hp,he,hi,ha⟩ := (SieveCompleteBoxing.mem_innerFamily D s z hD hs t).mp hi
    exact boxed_tuple_product_le D s z hD hs hz t false hp (hi.imp (fun h => h.le))
      (SieveBoxLength.accepts_level_mono _ D false 1 _
        (Real.rpow_le_self_of_one_le hD.le
          ((div_le_one (by linarith [SieveGeometricGrid.one_lt_ratio s hs])).mpr
            (SieveGeometricGrid.one_lt_ratio s hs).le)) ha)
  · obtain ⟨hp,he,hi,ha⟩ := (SieveCompleteBoxing.mem_outerFamily D s z hD hs t).mp ho
    exact boxed_tuple_product_le D s z hD hs hz t false hp hi ha

theorem upper_tuple_product_le (D s z : ℝ) (hD : 1<D) (hs : 0<s) (hz : z≤D)
    (t : List ℕ) (ht : t∈SieveUpperBoxing.outerFamily D s z ∪
      SieveUpperBoxing.innerFamily D s z) : (t.prod:ℝ)≤D^(SieveGeometricGrid.ratio s) := by
  rcases Finset.mem_union.mp ht with ho | hi
  · obtain ⟨hp,he,hi,ha⟩ := (SieveUpperBoxing.mem_outerFamily D s z hD hs t).mp ho
    exact boxed_tuple_product_le D s z hD hs hz t true hp hi ha
  · obtain ⟨hp,he,hi,ha⟩ := (SieveUpperBoxing.mem_innerFamily D s z hD hs t).mp hi
    exact boxed_tuple_product_le D s z hD hs hz t true hp (hi.imp (fun h => h.le))
      (SieveBoxLength.accepts_level_mono _ D true 1 _
        (Real.rpow_le_self_of_one_le hD.le
          ((div_le_one (by linarith [SieveGeometricGrid.one_lt_ratio s hs])).mpr
            (SieveGeometricGrid.one_lt_ratio s hs).le)) ha)

theorem smallCarrier_lt (D s : ℝ) (hD : 1<D) (hs : 0<s) (hs1 : s≤1)
    (d : ℕ) (hd : d∈SieveUpperBoxWindow.smallCarrier D s) : (d:ℝ)<D^s := by
  have hh := SieveSmallWeights.power_parameters D s hD hs hs1
  rcases Finset.mem_union.mp hd with hd | hd
  · exact SieveSmallWeights.support_lt _ _ false hh.1 hh.2 d hd
  · exact SieveSmallWeights.support_lt _ _ true hh.1 hh.2 d hd

theorem signed_support_le_square (D s : ℝ) (hD : 1<D) (hs : 0<s) (hsh : s≤1/2)
    (I O : Finset (List ℕ))
    (ht : ∀t∈I∪O, (t.prod:ℝ)≤D^(SieveGeometricGrid.ratio s))
    (m : ℕ) (hm : m∈SieveTupleConvolution.signedSupport
      (SieveUpperBoxWindow.smallCarrier D s) I O) : (m:ℝ)≤D^2 := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨ha,hb⟩ := Finset.mem_product.mp ha
  obtain ⟨t,ht',he⟩ := (SieveTupleConvolution.mem_tupleSupport _ _).mp hb
  have hsmall := (smallCarrier_lt D s hD hs (by linarith) a.1 ha).le
  have hlarge : (a.2:ℝ)≤D^(SieveGeometricGrid.ratio s) := by simpa only [he] using ht t ht'
  have h9 : s^9≤s := pow_le_of_le_one hs.le (by linarith) (by decide)
  have hexp : s+SieveGeometricGrid.ratio s≤2 := by unfold SieveGeometricGrid.ratio; linarith
  calc
    _ = (a.1:ℝ)*(a.2:ℝ) := by simp [DirichletProductCoefficients.productIndex]
    _ ≤ D^s*D^(SieveGeometricGrid.ratio s) :=
      mul_le_mul hsmall hlarge (Nat.cast_nonneg _) (Real.rpow_nonneg (by linarith) _)
    _ = D^(s+SieveGeometricGrid.ratio s) := (Real.rpow_add (by linarith) _ _).symm
    _ ≤ D^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hD.le hexp
    _ = D^2 := by norm_num

theorem lower_support_le_square (D s z : ℝ) (hD : 1<D) (hs : 0<s)
    (hsh : s≤1/2) (hz : z≤D) (m : ℕ) (hm : m∈SieveBoxedWindow.support D s z) :
    (m:ℝ)≤D^2 :=
  signed_support_le_square D s hD hs hsh _ _ (lower_tuple_product_le D s z hD hs hz) m hm

theorem upper_support_le_square (D s z : ℝ) (hD : 1<D) (hs : 0<s)
    (hsh : s≤1/2) (hz : z≤D) (m : ℕ) (hm : m∈SieveUpperBoxWindow.support D s z) :
    (m:ℝ)≤D^2 :=
  signed_support_le_square D s hD hs hsh _ _ (upper_tuple_product_le D s z hD hs hz) m hm

run_cmd do
  for decl in [``cubic_dominates_pair, ``lower_product_lt, ``upper_product_lt,
      ``scales_order, ``prod_le_power, ``boxed_tuple_product_le,
      ``lower_tuple_product_le, ``upper_tuple_product_le, ``smallCarrier_lt,
      ``signed_support_le_square, ``lower_support_le_square, ``upper_support_le_square] do
    for ax in (←Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL BOXED SUPPORT FROM CUBIC TESTS PASSED"

end PositiveSharpRemainderSupportGeometry
