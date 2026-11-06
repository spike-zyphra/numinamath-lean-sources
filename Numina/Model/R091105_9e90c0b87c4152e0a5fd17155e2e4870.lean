import Mathlib

theorem number_theory_268562 (n : ℕ) :
    n ∈ {n | n ∈ Finset.Icc 100 999 ∧ (n^2) % 1000 = (3 * n - 2)^2 % 1000} ↔
    n = 251 ∨ n = 501 ∨ n = 751 ∨ n = 313 ∨ n = 563 ∨ n = 813 := by
  simp only [Set.mem_setOf_eq, Finset.mem_Icc]
  constructor
  · -- Forward direction: If n is in the set and a three-digit number, then n is in the list
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, hn3⟩
    interval_cases n <;> norm_num at hn3 ⊢ <;> omega
  · -- Backward direction: If n is in the list, then n is in the set and a three-digit number
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · -- Verify n = 251
      constructor
      · norm_num
      · norm_num
    · -- Verify n = 501
      constructor
      · norm_num
      · norm_num
    · -- Verify n = 751
      constructor
      · norm_num
      · norm_num
    · -- Verify n = 313
      constructor
      · norm_num
      · norm_num
    · -- Verify n = 563
      constructor
      · norm_num
      · norm_num
    · -- Verify n = 813
      constructor
      · norm_num
      · norm_num