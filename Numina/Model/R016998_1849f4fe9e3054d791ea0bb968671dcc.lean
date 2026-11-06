import Mathlib

theorem algebra_10729 (x : ℕ) (h : (1 / 4 : ℚ) * 2^30 = 2^x) : x = 28 := by
  have eq1 : (2 : ℚ) ^ x = (2 : ℚ) ^ (28 : ℕ) := by
    have eq2 : (2 : ℚ) ^ x = (1 / 4 : ℚ) * 2^30 := by
      linarith [h]
    rw [eq2]
    norm_num
  have h2 : x = 28 := by
    have h3 : (2 : ℚ) ^ x = (2 : ℚ) ^ (28 : ℕ) := eq1
    have h4 : x = 28 := by
      exact Nat.cast_injective ((by simpa using h3 : (x : ℕ) = (28 : ℕ)))
    exact h4
  exact h2