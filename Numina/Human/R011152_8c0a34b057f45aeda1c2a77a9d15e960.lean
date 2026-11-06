import Mathlib

/-On New Year's Eve, Father Frost gave the children the following task: using all nine digits from 1 to 9 once each,
insert "+" or "-" between every two adjacent digits so that after performing the operations,
all possible two-digit prime numbers can be obtained. Help the children complete this task.
How many such numbers can be obtained-/

theorem number_theory_233476: {n: ℤ | 10 ≤ n ∧ n < 100 ∧ Prime n ∧
∃ a1 a2 a3 a4 a5 a6 a7 a8, (a1 = 1 ∨ a1 = -1) ∧ (a2 = a1 + 2 ∨ a2 = a1 - 2) ∧ (a3 = a2 + 3 ∨ a3 = a2 - 3) ∧
(a4 = a3 + 4 ∨ a4 = a3 - 4) ∧ (a5 = a4 + 5 ∨ a5 = a4 - 5) ∧ (a6 = a5 + 6 ∨ a6 = a5 - 6) ∧
(a7 = a6 + 7 ∨ a7 = a6 - 7) ∧ (a8 = a7 + 8 ∨ a8 = a7 - 8) ∧ (n = a8 + 9 ∨ n = a8 - 9)}
= {11, 13, 17, 19, 23, 29, 31, 37, 41, 43} := by

  ext n
  constructor
  -- the forward direction
  .
    intro h
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨ln1, ln2, pn, h⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h

    -- we show that n ≤ 45
    replace h2: a2 ≤ a1 + 2 := by
      omega
    replace h3: a3 ≤ a2 + 3 := by
      omega
    replace h4: a4 ≤ a3 + 4 := by
      omega
    replace h5: a5 ≤ a4 + 5 := by
      omega
    replace h6: a6 ≤ a5 + 6 := by
      omega
    replace h7: a7 ≤ a6 + 7 := by
      omega
    replace h8: a8 ≤ a7 + 8 := by
      omega
    have l: n ≤ 45 := by omega
    clear h2 h3 h4 h5 h6 h7 h8 h9 ln2
    simp
    interval_cases n
    all_goals norm_num at pn
    all_goals simp


  -- the backward direction
  .
    intro h
    simp only [Set.mem_setOf_eq]
    simp at h
    have o: 10 ≤ n ∧ n < 100 ∧ Prime n := by
      rcases h with h | h | h | h | h | h | h | h | h | h
      all_goals simp [h]; norm_num
    rcases o with ⟨o1, o2, o3⟩
    refine ⟨o1, o2, o3, ?_⟩
    rcases h with h | h | h | h | h | h | h | h | h | h
    all_goals clear o1 o2 o3

    -- n = 11
    .
      use 1, 3, 6, 10, 15, 21, 28, 20
      rw [h]
      omega

    -- n = 13
    .
      use 1, 3, 6, 10, 15, 21, 14, 22
      rw [h]
      omega

    -- n = 17
    .
      use 1, 3, 6, 10, 5, 11, 18, 26
      rw [h]
      omega

    -- n = 19
    .
      use 1, 3, 6, 2, 7, 13, 20, 28
      rw [h]
      omega

    -- n = 23
    .
      use 1, -1, 2, 6, 11, 17, 24, 32
      rw [h]
      omega

    -- n = 29
    .
      use 1, 3, 6, 10, 15, 21, 28, 20
      rw [h]
      omega

    -- n = 31
    .
      use 1, 3, 6, 10, 15, 21, 14, 22
      rw [h]
      omega

    -- n = 37
    .
      use 1, 3, 6, 2, 7, 13, 20, 28
      rw [h]
      omega

    -- n = 41
    .
      use 1, -1, 2, 6, 11, 17, 24, 32
      rw [h]
      omega

    -- n = 43
    .
      use -1, 1, 4, 8, 13, 19, 26, 34
      rw [h]
      omega
      