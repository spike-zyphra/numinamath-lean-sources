import Mathlib

theorem algebra_13273 :
  IsGreatest {x : ℝ | ∃ y : ℝ, x ^ 5 = 7 * y ^ 3 + 18 * y ∧ y ^ 5 = 7 * x ^ 3 + 18 * x} 3 := by
  constructor
  · -- Show that 3 is in the set
    use 3
    constructor
    · -- Show that 3^5 = 7 * 3^3 + 18 * 3
      norm_num
    · -- Show that 3^5 = 7 * 3^3 + 18 * 3
      norm_num
  · -- Show that 3 is greatest
    intro x hx
    rcases hx with ⟨y, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : y > 0 := by
      nlinarith [sq_nonneg (y ^ 2), sq_nonneg (y + 3), sq_nonneg (y - 3),
          sq_nonneg (x ^ 2 - 9), sq_nonneg (y ^ 2 - 9)]
    have h4 : y > 3 := by
      by_contra h4
      nlinarith [sq_nonneg (y ^ 2 - 9), sq_nonneg (y - 3), sq_nonneg (y + 3),
        sq_nonneg (x ^ 2 - 9), sq_nonneg (x - 3), sq_nonneg (x + 3),
        mul_pos (show x - 3 > 0 by nlinarith) (show x - 3 > 0 by nlinarith),
        sq_nonneg (y ^ 2), sq_nonneg ((y - 3) * (y + 3))]
    have h5 : x > 3 := by
      linarith
    nlinarith [sq_nonneg (x - y), sq_nonneg (x - 3), sq_nonneg (y - 3),
          sq_nonneg (x + 3), sq_nonneg (y + 3),
          sq_nonneg (x ^ 2 - 9), sq_nonneg (y ^ 2 - 9),
          mul_pos (show x - 3 > 0 by nlinarith) (show y - 3 > 0 by nlinarith),
          sq_nonneg (x ^ 4 - 81), sq_nonneg (y ^ 4 - 81)]