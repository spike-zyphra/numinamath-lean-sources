import Mathlib

/-What is the smallest integer greater than $38$ that cannot serve as the hypotenuse of a right triangle with integer side lengths?-/
theorem number_theory_4498 : IsLeast {n | n > 38 ∧ ¬∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = n^2} 42 := by
  constructor
  · -- Let's show that 42 is in our set.
    constructor
    · -- First, show 42 > 38
      norm_num
    · -- Now, we need to show 42 cannot be expressed as the sum of two positive squares.
      intro h
      rcases h with ⟨a, b, ha, hb, h_eq⟩
      have h1 : a ≤ 42 := by nlinarith
      have h2 : b ≤ 42 := by nlinarith
      interval_cases a <;> interval_cases b <;> omega
  · -- Now, we'll prove 42 is the smallest such number.
    intro n hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h1 : n = 39 ∨ n = 40 ∨ n = 41 := by omega
    rcases h1 with (rfl | rfl | rfl)
    · -- n = 39
      have h39 : ∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = 39^2 := ⟨36, 15, by norm_num, by norm_num, by norm_num⟩
      exact hn2 h39
    · -- n = 40
      have h40 : ∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = 40^2 := ⟨24, 32, by norm_num, by norm_num, by norm_num⟩
      exact hn2 h40
    · -- n = 41
      have h41 : ∃ a b, a > 0 ∧ b > 0 ∧ a^2 + b^2 = 41^2 := ⟨9, 40, by norm_num, by norm_num, by norm_num⟩
      exact hn2 h41