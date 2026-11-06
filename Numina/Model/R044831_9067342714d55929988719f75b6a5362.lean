import Mathlib

theorem number_theory_130238 (n : ℕ) : n ≠ 0 ∧ 2003 % n = 7 ↔ n = 499 ∨ n = 998 ∨ n = 1996 := by 
  constructor
  · -- Assume n ≠ 0 ∧ 2003 % n = 7, prove n = 499 ∨ n = 998 ∨ n = 1996
    intro h
    rcases h with ⟨hn, h1⟩
    have h2 : n ≤ 2003 := by
      by_contra h
      push_neg at h
      have h3 : 2003 % n = 2003 := by
        rw [Nat.mod_eq_of_lt]
        all_goals linarith
      omega
    interval_cases n <;> norm_num at h1 ⊢
    <;> tauto
  · -- Assume n = 499 ∨ n = 998 ∨ n = 1996, prove n ≠ 0 ∧ 2003 % n = 7
    rintro (h | h | h)
    · -- Assume n = 499
      rw [h]
      constructor
      · -- Show 499 ≠ 0
        norm_num
      · -- Show 2003 % 499 = 7
        norm_num
    · -- Assume n = 998
      rw [h]
      constructor
      · -- Show 998 ≠ 0
        norm_num
      · -- Show 2003 % 998 = 7
        norm_num
    · -- Assume n = 1996
      rw [h]
      constructor
      · -- Show 1996 ≠ 0
        norm_num
      · -- Show 2003 % 1996 = 7
        norm_num