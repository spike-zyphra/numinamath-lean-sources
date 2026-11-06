import Mathlib

theorem algebra_2465
    (roots : Set ℝ)
    (hroot : roots = {x : ℝ | x ^ 2 - 2 * x - 5 * abs (x - 1) + 7 = 0}) :
    ∑ᶠ x ∈ roots, x = 4 := by

  have h1 : roots = {4, 3, -1, -2} := by
    ext x
    simp [hroot]
    constructor
    · -- Assume x is a root, we need to prove x ∈ {4, 3, -1, -2}
      intro h_eq
      by_cases h : (x - 1 : ℝ) ≥ 0
      · -- In this case, |x - 1| = x - 1
        rw [abs_of_nonneg (by linarith)] at h_eq
        have h2 : x^2 - 7 * x + 12 = 0 := by linarith
        have h3 : (x - 3) * (x - 4) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h3) with h4 h5
        · -- Case where x = 3
          right
          left
          linarith
        · -- Case where x = 4
          left
          linarith
      · -- Case where x - 1 < 0, so |x - 1| = 1 - x
        rw [abs_of_neg (by linarith)] at h_eq
        have h6 : x^2 + 3 * x + 2 = 0 := by linarith
        have h7 : (x + 1) * (x + 2) = 0 := by
          nlinarith
        cases' (mul_eq_zero.mp h7) with h8 h9
        · -- Case where x = -1
          right
          right
          left
          linarith
        · -- Case where x = -2
          right
          right
          right
          linarith
    · -- Assume x ∈ {4, 3, -1, -2}, we need to prove x is a root
      rintro (rfl | rfl | rfl | rfl)
      · -- Check x = 4
        norm_num [abs_of_nonneg]
      · -- Check x = 3
        norm_num [abs_of_nonneg]
      · -- Check x = -1
        norm_num [abs_of_neg]
      · -- Check x = -2
        norm_num [abs_of_neg]

  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  norm_num
  all_goals norm_num
  all_goals norm_num