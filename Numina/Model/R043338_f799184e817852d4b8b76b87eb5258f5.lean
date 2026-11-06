import Mathlib

theorem algebra_14333 (x : ℕ) (h : (1 / 4 : ℝ) * 2^30 = 4^x) : x = 14 := by

  have eq1 : ( (1 / 4 : ℝ) * (2 ^ 30 : ℝ) ) = (4 ^ (x : ℕ) : ℝ) := by
    linarith [h]

  have eq2 : ( (1 / 4 : ℝ) * (2 ^ 30 : ℝ) ) = ( (2 : ℝ) ^ (28 : ℕ) ) := by
    norm_num

  have eq3 : ( (4 : ℝ) ^ (x : ℕ) ) = ( (2 : ℝ) ^ (2 * (x : ℕ) ) ) := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) by norm_num]
    rw [← pow_mul]

  rw [eq3] at eq1
  rw [eq2] at eq1

  have eq4 : (28 : ℕ) = 2 * (x : ℕ) := by
    exact Nat.cast_injective (by simpa using eq1)

  have : x = 14 := by
    omega

  exact this