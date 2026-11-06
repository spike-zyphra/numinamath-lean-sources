import Mathlib

theorem algebra_10439 : IsLeast {n : ℕ | ∃ a, ∃ b, (a ^ 2 - b ^ 2 = 133 ∧ n = a ^ 2 + b ^ 2)} 205 := by
  constructor
  · -- 205 is in the set
    use 13, 6
    all_goals norm_num
  · -- No smaller element is in the set
    intro n hn
    rcases hn with ⟨a, b, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : a ^ 2 - b ^ 2 = 133 := h1
    have h4 : n = a ^ 2 + b ^ 2 := by linarith
    have h5 : a ^ 2 = b ^ 2 + 133 := by
      omega
    have h6 : a ^ 2 + b ^ 2 < 205 := by
      linarith [h, h4]
    have h7 : b < 6 := by
      nlinarith
    have h8 : a < 13 := by
      nlinarith
    interval_cases b <;> interval_cases a <;> omega