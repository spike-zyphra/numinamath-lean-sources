import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_165634 (f : ℝ → ℝ → ℝ)
  (h₀ : ∀ x y, f x y = 2 * x ^ 2 - 2 * y ^ 2) :
  IsGreatest {z | ∃ x y, z = f x y ∧ x ^ 2 + y ^ 2 ≤ 9} 18 ∧
  IsLeast {z | ∃ x y, z = f x y ∧ x ^ 2 + y ^ 2 ≤ 9} (-18) := by
  constructor
  · -- Let's prove that 18 is the greatest element
    constructor
    · -- First we show that 18 is attained at (3, 0)
      use 3, 0
      constructor
      · -- Show that 18 = f(3, 0)
        rw [h₀ 3 0]
        norm_num
      · -- Show that 3 ^ 2 + 0 ^ 2 ≤ 9
        norm_num
    · -- Now we prove that 18 is an upper bound
      intro z h
      rcases h with ⟨x, y, h1, h2⟩
      rw [h₀ x y] at h1
      -- We need to show z = 2 * x ^ 2 - 2 * y ^ 2 ≤ 18.
      -- Since x² + y² ≤ 9, it follows that x² ≤ 9. Hence, 2 * x² ≤ 2 * 9 = 18.
      -- Since -2 * y² ≤ 0, it follows that 2 * x² - 2 * y² ≤ 18
      -- To prove 2 * x ^ 2 - 2 * y ^ 2 ≤ 18, we use constraints.
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x^2 + y^2 - 9), sq_nonneg (x - 3), sq_nonneg (y)]
  · -- Let's prove that -18 is the least element
    constructor
    · -- First we show that -18 is attained at (0, 3)
      use 0, 3
      constructor
      · -- Show that -18 = f(0, 3)
        rw [h₀ 0 3]
        norm_num
      · -- Show that 0 ^ 2 + 3 ^ 2 ≤ 9
        norm_num
    · -- Now we prove that -18 is a lower bound
      intro z h
      rcases h with ⟨x, y, h1, h2⟩
      rw [h₀ x y] at h1
      -- We need to show z = 2 * x ^ 2 - 2 * y ^ 2 ≥ -18.
      -- Since x² + y² ≤ 9, it follows that y² ≤ 9. Hence, -2 * y² ≥ -2 * 9 = -18.
      -- Since 2 * x^2 ≥ 0, it follows that 2 * x^2 - 2 * y^2 ≥ -18
      nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x^2 + y^2 - 9), sq_nonneg (x), sq_nonneg (y - 3)]