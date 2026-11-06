import Mathlib

theorem algebra_311008 :
    IsLeast {t : ℝ | ∃ x y z, t = abs x + abs y + abs z ∧ x * y * z = 32 ∧ x + y + z = 4} 12 := by
  constructor
  · -- Show 12 is in the set
    use -2, -2, 8
    norm_num [abs_of_neg, abs_of_pos]
    all_goals norm_num
  · -- Show that 12 is the minimum
    intro t ht
    rcases ht with ⟨x, y, z, ht_eq, h1, h2⟩
    by_cases h3 : x ≥ 0
    · -- Case x ≥0
      by_cases h4 : y ≥ 0
      · -- Case x ≥0, y ≥0
        by_cases h5 : z ≥ 0
        · -- Case x ≥0, y ≥0, z ≥0
          rw [abs_of_nonneg h3, abs_of_nonneg h4, abs_of_nonneg h5] at ht_eq
          nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), sq_nonneg (x - 2), sq_nonneg (y - 2), sq_nonneg (z - 2), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ y by nlinarith), mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ z by nlinarith), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ z by nlinarith)]
        · -- Case x ≥0, y ≥0, z <0
          rw [abs_of_nonneg h3, abs_of_nonneg h4, abs_of_neg (show z < 0 by linarith)] at ht_eq
          nlinarith [sq_nonneg (x - y), sq_nonneg (y + z), sq_nonneg (z + x), sq_nonneg (x - 4), sq_nonneg (y - 4), sq_nonneg (z + 8), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ y by nlinarith), mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ 0 - z by nlinarith), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ 0 - z by nlinarith)]
      · -- Case x ≥0, y <0
        by_cases h5 : z ≥ 0
        · -- Case x ≥0, y <0, z ≥0
          rw [abs_of_nonneg h3, abs_of_neg (show y < 0 by linarith), abs_of_nonneg (show z ≥ 0 by linarith)] at ht_eq
          nlinarith [sq_nonneg (x - 4), sq_nonneg (y + 2), sq_nonneg (z - 2), sq_nonneg (x - 8), sq_nonneg (y + 2), sq_nonneg (z - 2), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ 0 - y by nlinarith), mul_nonneg (show 0 ≤ 0 - y by nlinarith) (show 0 ≤ z by nlinarith), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ z by nlinarith)]
        · -- Case x ≥0, y <0, z <0
          rw [abs_of_nonneg h3, abs_of_neg (show y < 0 by linarith), abs_of_neg (show z < 0 by linarith)] at ht_eq
          nlinarith [sq_nonneg (x - 4), sq_nonneg (y + 2), sq_nonneg (z + 2), sq_nonneg (x - 8), sq_nonneg (y + 2), sq_nonneg (z + 2), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ 0 - y by nlinarith), mul_nonneg (show 0 ≤ 0 - y by nlinarith) (show 0 ≤ 0 - z by nlinarith), mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ 0 - z by nlinarith)]
    · -- Case x <0
      by_cases h4 : y ≥ 0
      · -- Case x <0, y ≥0
        by_cases h5 : z ≥ 0
        · -- Case x <0, y ≥0, z ≥0
          rw [abs_of_neg (show x < 0 by linarith), abs_of_nonneg h4, abs_of_nonneg h5] at ht_eq
          nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 2), sq_nonneg (z - 4), sq_nonneg (x + 2), sq_nonneg (y - 4), sq_nonneg (z - 4), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ y by nlinarith), mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ z by nlinarith), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ z by nlinarith)]
        · -- Case x <0, y ≥0, z <0
          rw [abs_of_neg (show x < 0 by linarith), abs_of_nonneg h4, abs_of_neg (show z < 0 by linarith)] at ht_eq
          nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 2), sq_nonneg (z + 2), sq_nonneg (x + 2), sq_nonneg (y - 4), sq_nonneg (z + 2), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ y by nlinarith), mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ 0 - z by nlinarith), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ 0 - z by nlinarith)]
      · -- Case x <0, y <0
        by_cases h5 : z ≥ 0
        · -- Case x <0, y <0, z ≥0
          rw [abs_of_neg (show x < 0 by linarith), abs_of_neg (show y < 0 by linarith), abs_of_nonneg h5] at ht_eq
          nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 2), sq_nonneg (z - 4), sq_nonneg (x + 2), sq_nonneg (y + 2), sq_nonneg (z - 8), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ 0 - y by nlinarith), mul_nonneg (show 0 ≤ 0 - y by nlinarith) (show 0 ≤ z by nlinarith), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ z by nlinarith)]
        · -- Case x <0, y <0, z <0
          rw [abs_of_neg (show x < 0 by linarith), abs_of_neg (show y < 0 by linarith), abs_of_neg (show z < 0 by linarith)] at ht_eq
          nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 2), sq_nonneg (z + 8), sq_nonneg (x + 2), sq_nonneg (y + 2), sq_nonneg (z + 8), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ 0 - y by nlinarith), mul_nonneg (show 0 ≤ 0 - y by nlinarith) (show 0 ≤ 0 - z by nlinarith), mul_nonneg (show 0 ≤ 0 - x by nlinarith) (show 0 ≤ 0 - z by nlinarith)]