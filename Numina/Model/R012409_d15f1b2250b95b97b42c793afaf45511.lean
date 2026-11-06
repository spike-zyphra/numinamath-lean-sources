import Mathlib

theorem algebra_3093 (x : ℕ) : (4 : ℝ) ^ x = (1 / 4) * 2 ^ 30 → x = 14 := by
  intro h
  have h1 : (4 : ℝ) ^ x = (2 : ℝ) ^ (2 * x : ℕ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
    rw [← pow_mul]
  have h2 : (1 / 4 : ℝ) * (2 : ℝ) ^ 30 = (2 : ℝ) ^ (28 : ℕ) := by
    norm_num
  rw [h1] at h
  rw [h2] at h
  have h3 : 2 * x = 28 := by
    have h4 : (2 : ℝ) ^ (2 * x : ℕ) = (2 : ℝ) ^ (28 : ℕ) := h
    have h5 : (2 * x : ℕ) = (28 : ℕ) := by
      exact Nat.cast_injective ((by simpa using h4) : (2 * x : ℕ) = (28 : ℕ))
    omega
  omega