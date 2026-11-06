import Mathlib

theorem algebra_242891 (n : ℤ) :
    ∃ m : ℤ, m^2 = n^2 + 4 * n - 5 ↔ n = 3 ∨ n = 1 ∨ n = -5 ∨ n = -7 := by
  use if n = 3 ∨ n = -7 then 4 else if n = 1 ∨ n = -5 then 0 else -4
  constructor
  · -- Forward implication: Assume m^2 = n^2 + 4 * n - 5, prove the goal.
    intro h
    by_cases h1 : n = 3 ∨ n = -7
    · -- Case 1: n = 3 ∨ n = -7.
      have hm : (if n = 3 ∨ n = -7 then 4 else if n = 1 ∨ n = -5 then 0 else -4) = 4 := by
        simp [h1]
      rw [hm] at h
      norm_num at h
      tauto
    · -- Case 2: ¬(n = 3 ∨ n = -7). 
      by_cases h2 : n = 1 ∨ n = -5
      · -- Case 2a: n = 1 ∨ n = -5.
        have hm : (if n = 3 ∨ n = -7 then 4 else if n = 1 ∨ n = -5 then 0 else -4) = 0 := by
          simp [h1, h2]
        rw [hm] at h
        norm_num at h
        rcases h2 with (h5 | h5)
        · -- If n = 1
          rw [h5] at *
          norm_num at *
          all_goals tauto
        · -- If n = -5
          rw [h5] at *
          norm_num at *
          all_goals tauto
      · -- Case 2b: ¬(n = 1 ∨ n = -5). 
        have hm : (if n = 3 ∨ n = -7 then 4 else if n = 1 ∨ n = -5 then 0 else -4) = -4 := by
          simp [h1, h2]
        rw [hm] at h
        norm_num at h
        have h3 : n = 3 ∨ n = -7 := by
          have h4 : n^2 + 4 * n - 21 = 0 := by
            nlinarith
          have h5 : (n - 3) * (n + 7) = 0 := by
            nlinarith
          cases' (mul_eq_zero.1 h5) with h6 h7
          · -- Case n - 3 = 0, so n = 3
            left
            linarith
          · -- Case n + 7 = 0, so n = -7
            right
            linarith
        have h4 : n = 3 ∨ n = -7 := h3
        have h5 : ¬(n = 3 ∨ n = -7) := by
          simpa using h1
        contradiction
  · -- Backward implication: Assume the goal, prove m^2 = n^2 + 4 * n - 5.
    intro h
    rcases h with (h | h | h | h)
    · -- n = 3
      rw [h]
      norm_num 
    · -- n = 1
      rw [h]
      norm_num 
    · -- n = -5
      rw [h]
      norm_num 
    · -- n = -7
      rw [h]
      norm_num