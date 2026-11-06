import Mathlib
set_option maxHeartbeats 999999999
namespace algebra_98051
lemma encard_prod {α β : Type*} (a : Set α) (b : Set β) :
    (a ×ˢ b).encard = a.encard * b.encard := by
  obtain rfl | hae := a.eq_empty_or_nonempty
  · simp
  obtain rfl | hbe := b.eq_empty_or_nonempty
  · simp
  obtain ha | ha := a.infinite_or_finite
  · rw [(ha.prod_left hbe).encard_eq, ha.encard_eq, ENat.top_mul hbe.encard_pos.ne']
  obtain hb | hb := b.infinite_or_finite
  · rw [(hb.prod_right hae).encard_eq, hb.encard_eq, ENat.mul_top hae.encard_pos.ne']
  rw [ha.encard_eq_coe_toFinset_card, hb.encard_eq_coe_toFinset_card]
  rw [(ha.prod hb).encard_eq_coe_toFinset_card, ← ENat.coe_mul, ENat.coe_inj]
  rw [← ha.toFinset_prod hb, Finset.card_product]
end algebra_98051
/- For integers $a,b,c$ and $d,$ let $f(x)=x^2+ax+b$ and $g(x)=x^2+cx+d.$ Find the number of ordered triples $(a,b,c)$ of integers with absolute values not exceeding $10$ for which there is an integer $d$ such that $g(f(2))=g(f(4))=0.$ -/
theorem algebra_98051 :
  Set.encard {(a, b, c) : ℤ × ℤ × ℤ | ∃ d : ℤ, -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧
    (2 ^ 2 + a * 2 + b) ^ 2 + c * (2 ^ 2 + a * 2 + b) + d = 0 ∧
    (4 ^ 2 + a * 4 + b) ^ 2 + c * (4 ^ 2 + a * 4 + b) + d = 0} = 510 := by
  -- split into two cases, a = -6 and a ≠ -6
  have spl : Set.encard {(a, b, c) : ℤ × ℤ × ℤ | ∃ d : ℤ, -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧
    (2 ^ 2 + a * 2 + b) ^ 2 + c * (2 ^ 2 + a * 2 + b) + d = 0 ∧
    (4 ^ 2 + a * 4 + b) ^ 2 + c * (4 ^ 2 + a * 4 + b) + d = 0} =
  Set.encard {(a, b, c) : ℤ × ℤ × ℤ | (∃ d : ℤ, -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧
    (2 ^ 2 + a * 2 + b) ^ 2 + c * (2 ^ 2 + a * 2 + b) + d = 0 ∧
    (4 ^ 2 + a * 4 + b) ^ 2 + c * (4 ^ 2 + a * 4 + b) + d = 0) ∧ a = -6} +
  Set.encard {(a, b, c) : ℤ × ℤ × ℤ | (∃ d : ℤ, -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧
    (2 ^ 2 + a * 2 + b) ^ 2 + c * (2 ^ 2 + a * 2 + b) + d = 0 ∧
    (4 ^ 2 + a * 4 + b) ^ 2 + c * (4 ^ 2 + a * 4 + b) + d = 0) ∧ a ≠ -6} := by
    rw [←Set.encard_union_eq]
    · apply congr_arg (fun x => Set.encard x)
      ext x
      obtain ⟨a, b, c⟩ := x
      simp only [Set.mem_setOf_eq, Set.mem_union]
      set qla := (∃ d : ℤ, -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧
    (2 ^ 2 + a * 2 + b) ^ 2 + c * (2 ^ 2 + a * 2 + b) + d = 0 ∧
    (4 ^ 2 + a * 4 + b) ^ 2 + c * (4 ^ 2 + a * 4 + b) + d = 0)
      constructor <;> intro h
      · by_cases hx : a = -6
        · left; constructor
          · assumption
          · exact hx
        · right; constructor
          · exact h
          · exact hx
      · obtain ⟨h, _⟩ | ⟨h, _⟩ := h
        all_goals exact h
    · rw [Set.disjoint_iff_inter_eq_empty]
      ext x
      obtain ⟨a, b, c⟩ := x
      simp only [Set.mem_union, Set.mem_setOf_eq]
      simp only [Int.reduceNeg, Int.reducePow, exists_and_left, ne_eq, Set.mem_inter_iff,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, Decidable.not_not, and_imp,
        forall_exists_index]
      tauto
  have eq1 : {(a, b, c) : ℤ × ℤ × ℤ | (∃ d : ℤ, -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧
    (2 ^ 2 + a * 2 + b) ^ 2 + c * (2 ^ 2 + a * 2 + b) + d = 0 ∧
    (4 ^ 2 + a * 4 + b) ^ 2 + c * (4 ^ 2 + a * 4 + b) + d = 0) ∧ a = -6} = {(a, b, c) : ℤ × ℤ × ℤ | -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧ a = -6} := by
    ext x
    obtain ⟨a, b, c⟩ := x
    simp only [Int.reduceNeg, Int.reducePow, exists_and_left, Set.mem_setOf_eq]
    constructor <;> intro h
    · tauto
    · obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only [Int.reduceNeg, h5, neg_le_neg_iff, Int.reduceLE, h1, h2, h3, h4, neg_mul,
        Int.reduceMul, Int.reduceAdd, and_self, true_and, and_true]
      exists -((-8 + b) ^ 2 + c * (-8 + b))
      ring
  -- intermediary lemma to count
  have eq11 : {(a, b, c) : ℤ × ℤ × ℤ | -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧ a = -6}.encard = (Set.Icc (-10) 10 ×ˢ Set.Icc (-10) 10).encard := by
    apply Set.encard_congr
    constructor
    -- forward function
    pick_goal 3
    · intro x
      obtain ⟨⟨a, b, c⟩, h⟩ := x
      simp only [Int.reduceNeg, Set.mem_setOf_eq] at h
      constructor
      pick_goal 2
      · exact ⟨b, c⟩
      · simp only [Int.reduceNeg, Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk]
        tauto
    -- inverse function
    pick_goal 3
    · intro x
      obtain ⟨⟨a, b⟩, h⟩ := x
      simp only [Int.reduceNeg, Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk] at h
      constructor
      pick_goal 2
      · exact ⟨-6, a, b⟩
      · simp only [Int.reduceNeg, Set.mem_setOf_eq, and_true]
        tauto
    -- is left inverse
    · intro x
      obtain ⟨⟨a, b, c⟩, h⟩ := x
      simp only [Int.reduceNeg, Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, Prod.mk.injEq, and_true]
      obtain ⟨_, _, _, _, rfl⟩ := h
      norm_num
    -- is right inverse
    · intro x
      obtain ⟨⟨a, b⟩, h⟩ := x
      simp only [Int.reduceNeg]
  rw [spl, eq1]; clear spl eq1
  rw [eq11]; clear eq11
  have := algebra_98051.encard_prod (@Set.Icc ℤ PartialOrder.toPreorder (-10) 10) (@Set.Icc ℤ PartialOrder.toPreorder (-10) 10)
  rw [this]; clear this
  -- compute cardinality of left set: it is 21 * 21 = 441
  have : (Set.Icc (-10) 10).encard = 21 := by
    rw [Set.encard.eq_1]
    simp only [Int.reduceNeg, ENat.card_eq_coe_fintype_card, Fintype.card_ofFinset, Int.card_Icc,
      Int.reduceAdd, sub_neg_eq_add, Int.reduceToNat, Nat.cast_ofNat]
  rw [this]; clear this; rw [(by norm_num : (21 : ENat) * 21 = 441)]
  -- now we explicitly enumerate the right set
  have nu : {(a, b, c) : ℤ × ℤ × ℤ | (∃ d : ℤ, -10 ≤ a ∧ a ≤ 10 ∧ -10 ≤ b ∧ b ≤ 10 ∧ -10 ≤ c ∧ c ≤ 10 ∧
    (2 ^ 2 + a * 2 + b) ^ 2 + c * (2 ^ 2 + a * 2 + b) + d = 0 ∧
    (4 ^ 2 + a * 4 + b) ^ 2 + c * (4 ^ 2 + a * 4 + b) + d = 0) ∧ a ≠ -6} = {(-8, 9, 10), (-8, 10, 8), (-7, 6, 10), (-7, 7, 8), (-7, 8, 6), (-7, 9, 4), (-7, 10, 2), (-5, 0, 10), (-5, 1, 8), (-5, 2, 6), (-5, 3, 4), (-5, 4, 2), (-5, 5, 0), (-5, 6, -2), (-5, 7, -4), (-5, 8, -6), (-5, 9, -8), (-5, 10, -10), (-4, -3, 10), (-4, -2, 8), (-4, -1, 6), (-4, 0, 4), (-4, 1, 2), (-4, 2, 0), (-4, 3, -2), (-4, 4, -4), (-4, 5, -6), (-4, 6, -8), (-4, 7, -10), (-3, -6, 10), (-3, -5, 8), (-3, -4, 6), (-3, -3, 4), (-3, -2, 2), (-3, -1, 0), (-3, 0, -2), (-3, 1, -4), (-3, 2, -6), (-3, 3, -8), (-3, 4, -10), (-2, -9, 10), (-2, -8, 8), (-2, -7, 6), (-2, -6, 4), (-2, -5, 2), (-2, -4, 0), (-2, -3, -2), (-2, -2, -4), (-2, -1, -6), (-2, 0, -8), (-2, 1, -10), (-1, -10, 6), (-1, -9, 4), (-1, -8, 2), (-1, -7, 0), (-1, -6, -2), (-1, -5, -4), (-1, -4, -6), (-1, -3, -8), (-1, -2, -10), (0, -10, 0), (0, -9, -2), (0, -8, -4), (0, -7, -6), (0, -6, -8), (0, -5, -10), (1, -10, -6), (1, -9, -8), (1, -8, -10)} := by
    ext x
    obtain ⟨a, b, c⟩ := x
    simp only [Int.reduceNeg, Int.reducePow, exists_and_left, Set.mem_setOf_eq,
      Set.mem_insert_iff, Prod.mk.injEq, Set.mem_singleton_iff]
    symm
    constructor <;> intro h
    -- they all satisfy the conditions
    · obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ := h
      all_goals clear * -
      all_goals constructor; pick_goal 2; native_decide; simp only [← and_assoc]; constructor; native_decide
      all_goals norm_num
      exists 21; exists 12; exists 24; exists 15; exists 8; exists 3; exists 24; exists 15; exists 8; exists 3; exists -1; exists 3; exists 8; exists 15; exists 24; exists 21; exists 12; exists 5; exists -3; exists -4; exists -3; exists 5; exists 12; exists 21; exists 16; exists 7; exists -5; exists -8; exists -9; exists -8; exists -5; exists 7; exists 16; exists 9; exists -7; exists -12; exists -15; exists -16; exists -15; exists -12; exists -7; exists 9; exists -16; exists -21; exists -24; exists -25; exists -24; exists -21; exists -16; exists -9; exists -36; exists -35; exists -32; exists -27; exists -20; exists -11; exists -40; exists -33; exists -24
    -- do case splits to enumerate
    · obtain ⟨⟨h1, h8, h3, h4, h5, h6, ⟨x, ⟨h9, h7⟩⟩⟩, h2⟩ := h
      have az : ((16 + 4 * a + b) - (4 + 2 * a + b)) * ((16 + 4 * a + b) + (4 + 2 * a + b) + c) = 0 := by ring_nf at *; linarith
      rw [mul_eq_zero] at az
      obtain az | az := az
      -- eliminate (16 + 4 * a + b) - (4 + 2 * a + b) = 0
      · exact False.elim (h2 (by linarith))
      -- now we are left with the latter term
      have s3 : c = -20 - 6 * a - 2 * b := by linarith
      clear h9 h7 az
      -- enumerate all a values
      obtain rf | rf | rf | rf | rf | rf | rf | rf | rf : a = -8 ∨ a = -7 ∨ a = -5 ∨ a = -4 ∨ a = -3 ∨ a = -2 ∨ a = -1 ∨ a = 0 ∨ a = 1 := by omega
      · subst a c; norm_num at *
        -- do magic
        have cut : 9 ≤ b := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : 6 ≤ b := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : 0 ≤ b := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : -3 ≤ b := by linarith
        have cu : b ≤ 7 := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : -6 ≤ b := by linarith
        have cu : b ≤ 4 := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : -9 ≤ b := by linarith
        have cu : b ≤ 1 := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : -10 ≤ b := by linarith
        have ct : b ≤ -2 := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : -10 ≤ b := by linarith
        have ct : b ≤ -5 := by linarith
        interval_cases b
        all_goals native_decide
      · subst a c; norm_num at *
        -- do magic
        have cut : -10 ≤ b := by linarith
        have ct : b ≤ -8 := by linarith
        interval_cases b
        all_goals native_decide
  rw [nu]
  (repeat rw [Set.encard_insert_of_not_mem]) <;> try native_decide
  rw [Set.encard_singleton]
  native_decide -- clear off arithmetic goal
  all_goals simp only [Int.reduceNeg, Set.mem_insert_iff, Prod.mk.injEq, neg_inj, OfNat.ofNat_eq_ofNat,
    Nat.succ_ne_self, Nat.reduceEqDiff, and_self, and_false, OfNat.ofNat_ne_one, neg_eq_zero,
    OfNat.ofNat_ne_zero, reduceCtorEq, and_true, Set.mem_singleton_iff, or_self, not_false_eq_true]
  all_goals try native_decide
  norm_num