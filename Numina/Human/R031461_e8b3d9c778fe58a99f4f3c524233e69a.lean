import Mathlib

/-A group of 25 friends were discussing a large positive integer. ``It can be divided by 1,'' said the first friend. ``It can be divided by 2,'' said the second friend. ``And by 3,'' said the third friend. ``And by 4,'' added the fourth friend. This continued until everyone had made such a comment. If exactly two friends were incorrect, and those two friends said consecutive numbers, what was the least possible integer they were discussing?-/
theorem number_theory_5471 :
  IsLeast {n | 0 < n ∧ (∃ k, ∀ m : Nat, (m ≥ 1 ∧ m ≤ 25 ∧ ¬(n % m = 0)) ↔ (m = k ∨ m = k + 1))} 787386600 := by
  -- first we make use of the definition of the minimum element of a set
  unfold IsLeast; simp only [ge_iff_le, Set.mem_setOf_eq, Nat.ofNat_pos, true_and]
  -- divide the problem into two parts: prove the answer is valid, and it is the smallest
  constructor
  -- from trial we know the integers not dividing the target integer are 16 and 17, and we put other numbers to the test
  use 16; simp only [Nat.reduceAdd]
  intro m; constructor
  rintro ⟨h₁, h₃, h₂⟩
  by_cases hyp : m = 1; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 2; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 3; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 4; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 5; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 6; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 7; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 8; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 9; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 10; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 11; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 12; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 13; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 14; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 15; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 18; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 19; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 20; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 21; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 22; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 23; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 24; rw [hyp] at h₂; absurd h₂; norm_num
  by_cases hyp : m = 25; rw [hyp] at h₂; absurd h₂; norm_num
  -- by testing all other integers less than 26 we close this part of the discussion
  omega
  -- as for 16 and 17 we check they do not devide the target number
  intro h; rcases h with h | h
  rw [h]; norm_num
  rw [h]; norm_num
  -- we make use of the definition of lowerBounds and split the statement
  unfold lowerBounds; simp only [Set.mem_setOf_eq, and_imp, forall_exists_index]
  intro a h₁ x h₂
  -- first we point out that 8 is a factor of the target, or otherwise 16 is also not a factor, leading to contradiction
  have t := h₂ 8
  simp only [ge_iff_le, Nat.one_le_ofNat, Nat.reduceLeDiff, Nat.mod_two_ne_zero,
    true_and, Nat.reduceEqDiff] at t
  by_cases prop₈ : a % 8 ≠ 0
  obtain c₁ | c₂ := t.mp prop₈
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t₂ := h₂ 16; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_self, iff_false, Decidable.not_not] at t₂
  have : 8 ∣ a := by
    apply dvd_of_mul_right_dvd
    pick_goal 2; use 2
    exact Nat.dvd_of_mod_eq_zero t₂
  absurd prop₈; exact (Nat.dvd_iff_mod_eq_zero).mp this
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t₂ := h₂ 16; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_self, iff_false, Decidable.not_not] at t₂
  have : 8 ∣ a := by
    apply dvd_of_mul_right_dvd
    pick_goal 2; use 2
    exact Nat.dvd_of_mod_eq_zero t₂
  absurd prop₈; exact (Nat.dvd_iff_mod_eq_zero).mp this
  push_neg at prop₈
  -- we point out that 9 is a factor of the target, or otherwise 18 is also not a factor, leading to contradiction
  have t₃ := h₂ 9; simp only [ge_iff_le, Nat.one_le_ofNat, Nat.reduceLeDiff, true_and,
    Nat.reduceEqDiff] at t₃
  by_cases prop₉ : a % 9 ≠ 0
  obtain c₁ | c₂ := t₃.mp prop₉
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t₄ := h₂ 18; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_self, iff_false, Decidable.not_not] at t₄
  have : 9 ∣ a := by
    apply dvd_of_mul_right_dvd
    pick_goal 2; use 2
    exact Nat.dvd_of_mod_eq_zero t₄
  absurd prop₉; exact (Nat.dvd_iff_mod_eq_zero).mp this
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t₄ := h₂ 18; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_self, iff_false, Decidable.not_not] at t₄
  have : 9 ∣ a := by
    apply dvd_of_mul_right_dvd
    pick_goal 2; use 2
    exact Nat.dvd_of_mod_eq_zero t₄
  absurd prop₉; exact (Nat.dvd_iff_mod_eq_zero).mp this
  push_neg at prop₉
  -- from the discussion above we know that 8 and 9 divides the target, therefore 24 = 72 / 3 is a factor
  have prop₂₄: 24 ∣ a := by apply Nat.dvd_trans; pick_goal 3; use 72; norm_num; refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₉)
  -- we point out that 7 is a factor of the target, or otherwise 14 is also not a factor, leading to contradiction
  have p₁ := h₂ 7; simp only [ge_iff_le, Nat.one_le_ofNat, Nat.reduceLeDiff, true_and,
    Nat.reduceEqDiff] at p₁
  by_cases prop₇ : a % 7 ≠ 0
  obtain c₁ | c₂ := p₁.mp prop₇
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t₄ := h₂ 14; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_self, iff_false, Decidable.not_not] at t₄
  have : 7 ∣ a := by
    apply dvd_of_mul_right_dvd
    pick_goal 2; use 2
    exact Nat.dvd_of_mod_eq_zero t₄
  absurd prop₇; exact (Nat.dvd_iff_mod_eq_zero).mp this
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t₄ := h₂ 14; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_self, iff_false, Decidable.not_not] at t₄
  have : 7 ∣ a := by
    apply dvd_of_mul_right_dvd
    pick_goal 2; use 2
    exact Nat.dvd_of_mod_eq_zero t₄
  absurd prop₇; exact (Nat.dvd_iff_mod_eq_zero).mp this
  push_neg at prop₇
  -- from the discussion above we know hat 7 and 8 divides the target, therefore 14 is a factor
  have prop₁₄: (2 * 7) ∣ a := Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (by apply Nat.dvd_trans; pick_goal 3; use 8; norm_num; exact Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₇)
  simp only [Nat.reduceMul] at prop₁₄
  -- from the discussion above we know hat 8 and 9 divides the target, therefore 12 is a factor
  have prop₁₂ : 12 ∣ a := by
    apply Nat.dvd_trans
    pick_goal 3; use 72; norm_num
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₉)
  -- as both 12 and 14 divide the target, according to the conditions 13 must divide the target
  have p₁ := h₂ 13; simp only [ge_iff_le, Nat.one_le_ofNat, Nat.reduceLeDiff, true_and,
    Nat.reduceEqDiff] at p₁
  by_cases prop₁₃ : a % 13 ≠ 0
  obtain c₁ | c₂ := p₁.mp prop₁₃
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t₄ := h₂ 14; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.succ_ne_self,
    or_true, iff_true] at t₄
  absurd t₄; apply (Nat.dvd_iff_mod_eq_zero).mp prop₁₄
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have r := h₂ 12; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_false, iff_true] at r
  absurd r; exact (Nat.dvd_iff_mod_eq_zero).mp prop₁₂
  push_neg at prop₁₃
  have t₅ := h₂ 25; simp only [ge_iff_le, Nat.one_le_ofNat, le_refl, true_and,
    Nat.reduceEqDiff] at t₅
  -- as 13 and 8 (therefore 26) and 24 divides the target, 25 must divide the target
  by_cases prop₂₅ : a % 25 ≠ 0
  obtain c₁ | c₂ := t₅.mp prop₂₅
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have r := h₂ 26; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, false_and, and_false,
    Nat.succ_ne_self, or_true, iff_true] at r
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have r := h₂ 24; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_false, iff_true] at r
  absurd r; exact (Nat.dvd_iff_mod_eq_zero).mp prop₂₄
  push_neg at prop₂₅
  -- as 25 and 8 (therefore 10) and 12 divides the target, 11 must divide the target
  have p := h₂ 11; simp only [ge_iff_le, Nat.one_le_ofNat, Nat.reduceLeDiff, true_and,
    Nat.reduceEqDiff] at p
  have prop₁₀ : 10 ∣ a := by
    apply Nat.dvd_trans
    pick_goal 3; use 200; norm_num
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₂₅)
  by_cases prop₁₁ : a % 11 ≠ 0
  obtain c₁ | c₂ := p.mp prop₁₁
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t := h₂ 12; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.succ_ne_self,
    or_true, iff_true] at t
  absurd t; exact (Nat.dvd_iff_mod_eq_zero).mp prop₁₂
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t := h₂ 10; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_false, iff_true] at t
  absurd t; exact (Nat.dvd_iff_mod_eq_zero).mp prop₁₀
  push_neg at prop₁₁
  -- as 9 and 8 (therefore 18), 8 and 25 (therefore 20) divides the target, 19 must divide the target
  have prop₁₈ : 18 ∣ a := by
    apply Nat.dvd_trans
    pick_goal 3; use 72; norm_num
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₉)
  have prop₂₀ : 20 ∣ a := by
    apply Nat.dvd_trans
    pick_goal 3; use 200; norm_num
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₂₅)
  have p := h₂ 19; simp only [ge_iff_le, Nat.one_le_ofNat, Nat.reduceLeDiff, true_and,
    Nat.reduceEqDiff] at p
  by_cases prop₁₉ : a % 19 ≠ 0
  obtain c₁ | c₂ := p.mp prop₁₉
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t := h₂ 20; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.succ_ne_self,
    or_true, iff_true] at t
  absurd t; exact (Nat.dvd_iff_mod_eq_zero).mp prop₂₀
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t := h₂ 18; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_false, iff_true] at t
  absurd t; exact (Nat.dvd_iff_mod_eq_zero).mp prop₁₈
  push_neg at prop₁₉
  -- as 8 and 11 (therefore 22) and 24 divides the target, 23 must divide the target
  have prop₂₂ : 22 ∣ a := by
    apply Nat.dvd_trans
    pick_goal 3; use 88; norm_num
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₁₁)
  have p := h₂ 23; simp only [ge_iff_le, Nat.one_le_ofNat, Nat.reduceLeDiff, true_and,
    Nat.reduceEqDiff] at p
  by_cases prop₂₃ : a % 23 ≠ 0
  obtain c₁ | c₂ := p.mp prop₂₃
  rw [← c₁] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t := h₂ 24; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.succ_ne_self,
    or_true, iff_true] at t
  absurd t; exact (Nat.dvd_iff_mod_eq_zero).mp prop₂₄
  rw [c₂] at h₂; simp only [ge_iff_le, Nat.reduceAdd] at h₂
  have t := h₂ 22; simp only [Nat.one_le_ofNat, Nat.reduceLeDiff, true_and, Nat.reduceEqDiff,
    or_false, iff_true] at t
  absurd t; exact (Nat.dvd_iff_mod_eq_zero).mp prop₂₂
  push_neg at prop₂₃
  -- combining the results above, 8 * 9 * 25 * 7 * 11 * 13 * 19 * 23 = 787386600 divides the target, and the target must be no less than this number, which closes the discussion
  have : (8 * 9 * 25 * 7 * 11 * 13 * 19 * 23) ∣ a := Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (Nat.Coprime.mul_dvd_of_dvd_of_dvd rfl (Nat.dvd_of_mod_eq_zero prop₈) (Nat.dvd_of_mod_eq_zero prop₉)) (Nat.dvd_of_mod_eq_zero prop₂₅)) (Nat.dvd_of_mod_eq_zero prop₇)) (Nat.dvd_of_mod_eq_zero prop₁₁)) (Nat.dvd_of_mod_eq_zero prop₁₃)) (Nat.dvd_of_mod_eq_zero prop₁₉)) (Nat.dvd_of_mod_eq_zero prop₂₃)
  exact Nat.le_of_dvd h₁ this
