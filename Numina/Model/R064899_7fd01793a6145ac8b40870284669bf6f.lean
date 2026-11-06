import Mathlib

theorem algebra_261772 : (2^n : ℝ) = 8^20 ↔ n = 60 := by
  constructor
  · -- Assume (2^n : ℝ) = 8^20, prove n = 60
    intro h
    have h1 : (8 ^ 20 : ℝ) = (2 ^ 60 : ℝ) := by
      norm_num
    rw [h1] at h
    have h2' : (2 : ℝ) ^ (n : ℕ) = (2 : ℝ) ^ (60 : ℕ) := by
      norm_cast at h ⊢
    have h3 : n = 60 := by
      exact Nat.cast_injective (by simpa using h2')
    exact h3
  · -- Assume n = 60, prove (2^n : ℝ) = 8^20
    intro h
    rw [h]
    have h1 : (8 : ℝ) ^ 20 = (2 : ℝ) ^ 60 := by
      norm_num
    norm_num at h1 ⊢
    all_goals linarith [h1]