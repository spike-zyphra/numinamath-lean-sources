import Mathlib

/-The sum of ten different non-zero natural numbers is 102.
What is the maximum value of the sum of the two largest numbers?
What is the minimum value of the sum of the two smallest numbers?-/

theorem number_theory_125499: IsGreatest {n : ℕ | ∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, n = a9 + a10 ∧
0 < a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 < a6 ∧ a6 < a7 ∧ a7 < a8 ∧
  a8 < a9 ∧ a9 < a10 ∧ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 = 102} 66 ∧

  IsLeast {n : ℕ | ∃ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10, n = a1 + a2 ∧
0 < a1 ∧ a1 < a2 ∧ a2 < a3 ∧ a3 < a4 ∧ a4 < a5 ∧ a5 < a6 ∧ a6 < a7 ∧ a7 < a8 ∧
  a8 < a9 ∧ a9 < a10 ∧ a1 + a2 + a3 + a4 + a5 + a6 + a7 + a8 + a9 + a10 = 102} 3 := by

  constructor

  -- show the largest sum is 66
  .
    constructor

    -- show 66 is in the set
    .
      simp only [Set.mem_setOf_eq]
      use 1
      use 2
      use 3
      use 4
      use 5
      use 6
      use 7
      use 8
      use 9
      use 57
      norm_num

    -- show the sum is at most 66
    .
      intro n h
      simp only [Set.mem_setOf_eq] at h
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, h⟩ := h
      rcases h with ⟨hn, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, s⟩
      simp [hn]
      clear hn
      nlinarith  -- since i ≤ ai


  -- show the smallest sum is 3
  .
    constructor

    -- show 3 is in the set
    .
      simp only [Set.mem_setOf_eq]
      use 1
      use 2
      use 3
      use 4
      use 5
      use 6
      use 7
      use 8
      use 9
      use 57
      norm_num

    -- show the sum is at least 3
    .
      intro n h
      simp only [Set.mem_setOf_eq] at h
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, h⟩ := h
      rcases h with ⟨hn, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, s⟩
      simp [hn]
      clear hn
      nlinarith  -- since i ≤ ai