import Mathlib

theorem algebra_114172 (x : ℕ) :
    x * (x - 1) * (x - 2) + (100 - x) * (99 - x) * (98 - x) ≠ 0 := by
  cases' le_or_lt x 100 with h h
  · -- Case x ≤ 100
    have h1 : x ≤ 100 := h
    by_cases h2 : x ≤ 98
    · -- Case x ≤ 98
      interval_cases x <;> omega
    · -- Case 98 < x ≤ 100
      have h2 : x = 99 ∨ x = 100 := by
        omega
      rcases h2 with (r | r)
      · -- Case x = 99
        subst x
        all_goals
        omega
      · -- Case x = 100
        subst x
        all_goals
        omega
  · -- Case x > 100
    have h2 : x > 100 := h
    have h3 : 100 - x = 0 := by
      omega
    have h4 : (100 - x) * (99 - x) * (98 - x) = 0 := by
      rw [h3]
      all_goals
      norm_num
    have h5 : x * (x - 1) * (x - 2) > 0 := by
      have hx1 : x > 0 := by
        omega
      have hx2 : x - 1 > 0 := by
        omega
      have hx3 : x - 2 > 0 := by
        omega
      have hx4 : x * (x - 1) * (x - 2) > 0 := by
        apply Nat.mul_pos
        apply Nat.mul_pos
        all_goals
        omega
      exact hx4
    have h6 : x * (x - 1) * (x - 2) + (100 - x) * (99 - x) * (98 - x) = x * (x - 1) * (x - 2) := by
      rw [h4]
      all_goals
      omega
    rw [h6]
    all_goals
    linarith