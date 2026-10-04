import ShortSingletonGeometry

/-! Actual upper-family third-prime and complete-product
geometry. Weak descent is imposed on geometric indices, never on the
actual outer prime entries. No mean estimate is asserted by this file. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section

namespace LongerTupleGeometry
open SieveWeightedCutoffs SieveBoxedFamily SieveGeometricGrid
open UpperAfter545Geometry

theorem ninth_le_half (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    s^9 ≤ s/2 := by
  have hp8 : s^8 ≤ (1/1000:ℝ)^8 := pow_le_pow_left₀ hs.le hs1 8
  have hp8' : s^8 ≤ (1/2:ℝ) := hp8.trans (by norm_num)
  calc
    s^9 = s*s^8 := by ring
    _ ≤ s*(1/2) := mul_le_mul_of_nonneg_left hp8' hs.le
    _ = s/2 := by ring

theorem ratio_fifth_lt (s : ℝ) (hs : 0 < s) (hs1 : s ≤ 1/1000) :
    ratio s/5 < (201/1000:ℝ) := by
  have hh := ninth_le_half s hs hs1
  unfold ratio
  linarith

theorem scales_pairwise (D s : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) (hi : (indices D s t).Pairwise (· ≥ ·)) :
    (scales D s t).Pairwise (· ≥ ·) := by
  rw [indices, List.pairwise_map] at hi
  rw [scales, List.pairwise_map]
  exact hi.imp (fun hpq => (scale_strictMono D s hD hs).monotone hpq)

/-- The stronger inner level may be weakened here without changing any
actual tuple membership. All outer repetitions remain permitted. -/
theorem family_data (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ)
    (ht : t ∈ SieveUpperBoxing.outerFamily D s z ∨
      t ∈ SieveUpperBoxing.innerFamily D s z) :
    (∀ q ∈ t, q ∈ pool D s z) ∧
      (scales D s t).Pairwise (· ≥ ·) ∧
      SieveBoxPrefix.accepts D true 1 (scales D s t) := by
  rcases ht with ht | ht
  · obtain ⟨hp,ha⟩ := (SieveUpperBoxing.mem_outerFamily D s z hD hs t).mp ht
    exact ⟨hp, scales_pairwise D s hD hs t ha.2.1, ha.2.2⟩
  · obtain ⟨hp,ha⟩ := (SieveUpperBoxing.mem_innerFamily D s z hD hs t).mp ht
    have hi := ha.2.1.imp (fun h => h.le)
    have hr : 1 ≤ ratio s := (one_lt_ratio s hs).le
    have hlevel : D^(1/ratio s) ≤ D :=
      Real.rpow_le_self_of_one_le hD.le
        ((div_le_one (by linarith : 0 < ratio s)).mpr hr)
    exact ⟨hp, scales_pairwise D s hD hs t hi,
      SieveBoxLength.accepts_level_mono (D^(1/ratio s)) D true 1
        (scales D s t) hlevel ha.2.2⟩

theorem fifth_le_prefix (a b c : ℝ) (hc : 0 ≤ c)
    (hca : c ≤ a) (hcb : c ≤ b) : c^5 ≤ a*b*c^3 := by
  have hcc : c*c ≤ a*b := mul_le_mul hca hcb hc (hc.trans hca)
  have hh := mul_le_mul_of_nonneg_right hcc (pow_nonneg hc 3)
  nlinarith

/-- The actual prefix test at index 2 bounds the third coordinate. -/
theorem third_coordinate_fifth_lt (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (a b c : ℕ) (tail : List ℕ)
    (ht : a::b::c::tail ∈ SieveUpperBoxing.outerFamily D s z ∨
      a::b::c::tail ∈ SieveUpperBoxing.innerFamily D s z) :
    (coordinate D s c)^5 < D := by
  obtain ⟨_,ho,ha⟩ := family_data D s z hD hs (a::b::c::tail) ht
  have ho' : (coordinate D s a :: coordinate D s b ::
      coordinate D s c :: scales D s tail).Pairwise (· ≥ ·) := by
    simpa only [scales, List.map_cons] using ho
  have hca : coordinate D s c ≤ coordinate D s a :=
    (List.pairwise_cons.mp ho').1 _ (by simp)
  have hcb : coordinate D s c ≤ coordinate D s b :=
    (List.pairwise_cons.mp (List.pairwise_cons.mp ho').2).1 _ (by simp)
  have htest := (SieveBoxPrefix.accepts_iff_prefix_tests D true 1
    (scales D s (a::b::c::tail))).mp ha 2 (by simp [scales]) (by decide)
  have htest' : coordinate D s a * coordinate D s b *
      (coordinate D s c)^3 < D := by
    simpa [scales, List.take, mul_assoc] using htest
  have hc : 0 ≤ coordinate D s c := Real.rpow_nonneg (by linarith) _
  exact (fifth_le_prefix _ _ _ hc hca hcb).trans_lt htest'

theorem prime_lt_ratio_fifth (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (a b c : ℕ) (tail : List ℕ)
    (ht : a::b::c::tail ∈ SieveUpperBoxing.outerFamily D s z ∨
      a::b::c::tail ∈ SieveUpperBoxing.innerFamily D s z) :
    (c:ℝ) < D^(ratio s/5) := by
  have hcPool := (family_data D s z hD hs (a::b::c::tail) ht).1 c (by simp)
  have hc0 : (0:ℝ) < c := by exact_mod_cast ((mem_pool D s z c).mp hcPool).1.pos
  have hcoord1 : 1 ≤ coordinate D s c :=
    (Real.one_le_rpow hD.le (sq_nonneg s)).trans
      (SieveCompleteBoxing.coordinate_ge_initial D s hD hs c)
  have hcoord0 : 0 < coordinate D s c := by linarith
  have hD0 : 0 < D := by linarith
  have hr : 0 < ratio s := lt_trans zero_lt_one (one_lt_ratio s hs)
  have hq := Real.log_lt_log hc0 (coordinate_bounds D s z hD hs hz c hcPool).2.2
  rw [Real.log_rpow hcoord0] at hq
  have hc := Real.log_lt_log (pow_pos hcoord0 5)
    (third_coordinate_fifth_lt D s z hD hs a b c tail ht)
  rw [Real.log_pow] at hc
  have hm := mul_lt_mul_of_pos_left hc hr
  apply (Real.log_lt_log_iff hc0 (Real.rpow_pos_of_pos hD0 _)).mp
  rw [Real.log_rpow hD0]
  norm_num at hc hm
  nlinarith

theorem third_prime_lt_point201 (X D s z : ℝ) (hX : 1 < X)
    (hD : 1 < D) (hDX : D ≤ X) (hs : 0 < s) (hs1 : s ≤ 1/1000)
    (hz : z ≤ D) (a b c : ℕ) (tail : List ℕ)
    (ht : a::b::c::tail ∈ SieveUpperBoxing.outerFamily D s z ∨
      a::b::c::tail ∈ SieveUpperBoxing.innerFamily D s z) :
    (c:ℝ) < X^(201/1000:ℝ) := by
  have hr : 0 ≤ ratio s/5 := by linarith [one_lt_ratio s hs]
  exact (prime_lt_ratio_fifth D s z hD hs hz a b c tail ht).trans_le
    ((Real.rpow_le_rpow (by linarith) hDX hr).trans
      (Real.rpow_le_rpow_of_exponent_le hX.le (ratio_fifth_lt s hs hs1).le))

/-- A numerical support lemma for every nonempty upper-tested list.
The proof uses pairs of entries and their coordinate order. -/
theorem accepted_product_lt (D d : ℝ) (xs : List ℝ) (hd : 0 < d)
    (hx : ∀ x ∈ xs, 1 ≤ x) (ho : xs.Pairwise (· ≥ ·))
    (ha : SieveBoxPrefix.accepts D true d xs) (hne : xs ≠ []) :
    d*xs.prod < D := by
  induction xs using List.twoStepInduction generalizing d with
  | nil => exact (hne rfl).elim
  | singleton a =>
      have ha1 := hx a (by simp)
      have hc : d*a^3 < D := by simpa [SieveBoxPrefix.accepts] using ha
      have hap : a ≤ a^3 := by
        simpa using pow_le_pow_right₀ ha1 (by decide : (1:ℕ) ≤ 3)
      simpa using (mul_le_mul_of_nonneg_left hap hd.le).trans_lt hc
  | cons_cons a b xs ih _ =>
      have ha1 := hx a (by simp)
      have hb1 := hx b (by simp)
      have hba : b ≤ a := (List.pairwise_cons.mp ho).1 b (by simp)
      have htail : SieveBoxPrefix.accepts D true (d*a*b) xs := ha.2.2
      by_cases he : xs = []
      · subst xs
        have hc : d*a^3 < D := by
          simpa only [SieveBoxPrefix.accepts, Bool.true_eq_false,
            false_or] using ha.1
        have hab : a*b ≤ a^2 := by nlinarith
        have haa : a^2 ≤ a^3 :=
          pow_le_pow_right₀ ha1 (by decide : (2:ℕ) ≤ 3)
        have hh := (mul_le_mul_of_nonneg_left (hab.trans haa) hd.le).trans_lt hc
        simpa [mul_assoc] using hh
      · have hxt : ∀ x ∈ xs, 1 ≤ x := fun x hx' => hx x (by simp [hx'])
        have hot := (List.pairwise_cons.mp (List.pairwise_cons.mp ho).2).2
        have hr := ih (d*a*b) (by positivity) hxt hot htail he
        simpa [mul_assoc] using hr

theorem coordinate_product_lt (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (t : List ℕ) (hne : t ≠ [])
    (ht : t ∈ SieveUpperBoxing.outerFamily D s z ∨
      t ∈ SieveUpperBoxing.innerFamily D s z) :
    (scales D s t).prod < D := by
  obtain ⟨_,ho,ha⟩ := family_data D s z hD hs t ht
  have hx : ∀ x ∈ scales D s t, 1 ≤ x := fun x hx =>
    (Real.one_le_rpow hD.le (sq_nonneg s)).trans
      (SieveCompleteBoxing.scales_ge_initial D s hD hs t x hx)
  have he : scales D s t ≠ [] := by
    cases t with
    | nil => exact (hne rfl).elim
    | cons q t => simp [scales]
  simpa using accepted_product_lt D 1 (scales D s t) (by norm_num) hx ho ha he

theorem cast_prod_le_coordinate_product (D s z : ℝ) (hD : 1 < D)
    (hs : 0 < s) (hz : z ≤ D) (t : List ℕ)
    (hp : ∀ q ∈ t, q ∈ pool D s z) :
    (t.prod:ℝ) ≤ (scales D s t).prod ^ ratio s := by
  induction t with
  | nil => simp [scales]
  | cons q t ih =>
      have hq := coordinate_bounds D s z hD hs hz q (hp q (by simp))
      have hpt : ∀ a ∈ t, a ∈ pool D s z := fun a ha => hp a (by simp [ha])
      have ht0 : 0 ≤ (scales D s t).prod := List.prod_nonneg (fun x hx =>
        (Real.rpow_nonneg (by linarith : 0 ≤ D) (s^2)).trans
          (SieveCompleteBoxing.scales_ge_initial D s hD hs t x hx))
      have hh := mul_le_mul hq.2.2.le (ih hpt) (Nat.cast_nonneg _)
        (Real.rpow_nonneg hq.1 (ratio s))
      simp only [scales, List.map_cons, List.prod_cons, Nat.cast_mul]
      change (q:ℝ)*(t.prod:ℝ) ≤
        (coordinate D s q*(scales D s t).prod)^ratio s
      rw [Real.mul_rpow hq.1 ht0]
      exact hh

theorem actual_tuple_product_lt (D s z : ℝ) (hD : 1 < D) (hs : 0 < s)
    (hz : z ≤ D) (t : List ℕ) (hne : t ≠ [])
    (ht : t ∈ SieveUpperBoxing.outerFamily D s z ∨
      t ∈ SieveUpperBoxing.innerFamily D s z) :
    (t.prod:ℝ) < D^ratio s := by
  have hp := (family_data D s z hD hs t ht).1
  have ht0 : 0 ≤ (scales D s t).prod := List.prod_nonneg (fun x hx =>
    (Real.rpow_nonneg (by linarith : 0 ≤ D) (s^2)).trans
      (SieveCompleteBoxing.scales_ge_initial D s hD hs t x hx))
  exact (cast_prod_le_coordinate_product D s z hD hs hz t hp).trans_lt
    (Real.rpow_lt_rpow ht0 (coordinate_product_lt D s z hD hs t hne ht)
      (lt_trans zero_lt_one (one_lt_ratio s hs)))

/-- Complete physical support bound, including the actual small divisor. -/
theorem physical_product_lt (X s z : ℝ) (p d : ℕ) (t : List ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000) (hp : 0 < p)
    (hD : 1 < level X s/p) (hz : z ≤ level X s/p)
    (hd : d ∈ SieveUpperBoxWindow.smallCarrier (level X s/p) s)
    (hne : t ≠ [])
    (ht : t ∈ SieveUpperBoxing.outerFamily (level X s/p) s z ∨
      t ∈ SieveUpperBoxing.innerFamily (level X s/p) s z) :
    ((p*d*t.prod:ℕ):ℝ) < X^(1-3*s/2) := by
  let D : ℝ := level X s/p
  have hX0 : 0 < X := by linarith
  have hD0 : 0 < D := by dsimp [D]; linarith
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hd0 : (0:ℝ) < d := by exact_mod_cast smallCarrier_pos _ _ d hd
  have hsmall : (d:ℝ) < D^s :=
    PositiveSharpRemainderSupportGeometry.smallCarrier_lt _ _ hD hs (by linarith) d hd
  have htuple : (t.prod:ℝ) < D^ratio s :=
    actual_tuple_product_lt D s z hD hs hz t hne ht
  have hDX : D ≤ X :=
    (div_le_self (Real.rpow_nonneg hX0.le _) hp1).trans
      (PositiveSharpRemainderSupport.level_le_X X s hX.le hs.le)
  have hpD : (p:ℝ)*D = X^(1-3*s) := by
    dsimp [D, level]
    field_simp
  have he : D^(s+ratio s) = D*D^(s+s^9) := by
    calc
      _ = D^(1+(s+s^9)) := by congr 1; unfold ratio; ring
      _ = D^1*D^(s+s^9) := Real.rpow_add hD0 _ _
      _ = _ := by rw [Real.rpow_one]
  have hds : (d:ℝ)*(t.prod:ℝ) < D^s*D^ratio s :=
    (mul_lt_mul_of_pos_left htuple hd0).trans_le
      (mul_le_mul_of_nonneg_right hsmall.le (by positivity))
  calc
    ((p*d*t.prod:ℕ):ℝ) = (p:ℝ)*((d:ℝ)*(t.prod:ℝ)) := by push_cast; ring
    _ < (p:ℝ)*(D^s*D^ratio s) := mul_lt_mul_of_pos_left hds hp0
    _ = (p:ℝ)*D^(s+ratio s) := by rw [Real.rpow_add hD0]
    _ = X^(1-3*s)*D^(s+s^9) := by rw [he, ←mul_assoc, hpD]
    _ ≤ X^(1-3*s)*X^(s+s^9) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hD0.le hDX (by positivity)) (by positivity)
    _ = X^(1-2*s+s^9) := by rw [←Real.rpow_add hX0]; congr 1; ring
    _ ≤ X^(1-3*s/2) := Real.rpow_le_rpow_of_exponent_le hX.le
      (by linarith [ninth_le_half s hs hs1])

theorem third_prime_bounds (X s z : ℝ) (p a b c : ℕ) (tail : List ℕ)
    (hX : 1 < X) (hs : 0 < s) (hs1 : s ≤ 1/1000)
    (hlog : 1000 ≤ Real.log X) (hp : 0 < p)
    (hptop : (p:ℝ) ≤ Real.sqrt (2*X)) (hD : 1 < level X s/p)
    (hz : z ≤ level X s/p)
    (ht : a::b::c::tail ∈ SieveUpperBoxing.outerFamily (level X s/p) s z ∨
      a::b::c::tail ∈ SieveUpperBoxing.innerFamily (level X s/p) s z) :
    c.Prime ∧ X^((49/100:ℝ)*s^2) ≤ (c:ℝ) ∧ (c:ℝ) < X^(201/1000:ℝ) := by
  have hX0 : 0 < X := by linarith
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hD0 : 0 < level X s/p := by linarith
  have hDX : level X s/p ≤ X :=
    (div_le_self (Real.rpow_nonneg hX0.le _) hp1).trans
      (PositiveSharpRemainderSupport.level_le_X X s hX.le hs.le)
  have hpcap := hptop.trans (ShortSingletonGeometry.sqrt_two_mul_le X hX hlog)
  have hDlo : X^(49/100:ℝ) ≤ level X s/p := by
    apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hX0 _) hD0).mp
    rw [Real.log_rpow hX0, level,
      Real.log_div (Real.rpow_pos_of_pos hX0 _).ne' hp0.ne', Real.log_rpow hX0]
    have hpLog := Real.log_le_log hp0 hpcap
    rw [Real.log_rpow hX0] at hpLog
    have hsLog := mul_le_mul_of_nonneg_right hs1 (Real.log_pos hX).le
    nlinarith
  have hcPool := (family_data _ s z hD hs (a::b::c::tail) ht).1 c (by simp)
  have hc := (mem_pool _ s z c).mp hcPool
  refine ⟨hc.1, ?_, third_prime_lt_point201 X _ s z hX hD hDX hs hs1 hz a b c tail ht⟩
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hX0.le _) hDlo (sq_nonneg s)
  rw [←Real.rpow_mul hX0.le] at hh
  exact hh.trans hc.2.2

run_cmd do
  for decl in [``ninth_le_half, ``ratio_fifth_lt, ``scales_pairwise, ``family_data,
      ``fifth_le_prefix, ``third_coordinate_fifth_lt, ``prime_lt_ratio_fifth,
      ``third_prime_lt_point201, ``accepted_product_lt, ``coordinate_product_lt,
      ``cast_prod_le_coordinate_product, ``actual_tuple_product_lt,
      ``physical_product_lt, ``third_prime_bounds] do
    for ax in (← Lean.collectAxioms decl) do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {decl}"
  Lean.logInfo "ACTUAL LONGER UPPER TUPLE GEOMETRY PASSED"

end LongerTupleGeometry
