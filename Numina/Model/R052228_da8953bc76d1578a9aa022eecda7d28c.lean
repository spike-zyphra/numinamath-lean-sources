import Mathlib

theorem algebra_21159 (x : ℕ) : 2^3 * 3^x = 72 ↔ x = 2 := by 
  constructor
  · -- Forward direction: If 2^3 * 3^x = 72, then x = 2
    intro h
    have h1 : 3 ^ x = 9 := by
      have h2 : 2^3 * 3^x = 72 := h
      have h3 : 3 ^ x = 9 := by
        omega
      exact h3
    have h3 : x = 2 := by
      have h4 : 3 ^ x = 9 := h1
      have eq1 : 3 ^ 2 = 9 := by norm_num
      rw [← eq1] at h4
      have h5 : x = (2 : ℕ) := by
        exact Nat.pow_right_injective (by norm_num) h4
      exact h5
    exact h3
  · -- Backward direction: If x = 2, then 2^3 * 3^x = 72
    intro h
    rw [h]
    all_goals norm_num