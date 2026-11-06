import Mathlib

theorem algebra_412 :
  IsGreatest {t : ℝ | ∃ x y, t = x * y ∧ (x - 3)^2 + (y - 3)^2 = 4} ((3 + Real.sqrt 2)^2) ∧
  IsLeast {t : ℝ | ∃ x y, t = x * y ∧ (x - 3)^2 + (y - 3)^2 = 4} ((3 - Real.sqrt 2)^2) := by
  constructor
  · -- First, we prove that (3 + Real.sqrt 2)^2 is greatest
    constructor
    · -- Show that (3 + Real.sqrt 2)^2 is in the set
      use (3 + Real.sqrt 2), (3 + Real.sqrt 2)
      constructor
      · -- Show the product equals (3 + Real.sqrt 2) ^ 2
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      · -- Show the pair satisfies the circle equation
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · -- Show that (3 + Real.sqrt 2) ^ 2 is greatest
      intro t ht
      rcases ht with ⟨x, y, h_eq, h_eq1⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 6), sq_nonneg (x - 3 - (y - 3)), sq_nonneg (x - 3 - Real.sqrt 2), sq_nonneg (y - 3 - Real.sqrt 2), sq_nonneg (x - 3 + Real.sqrt 2), sq_nonneg (y - 3 + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Second, we prove that (3 - Real.sqrt 2)^2 is least
    constructor
    · -- Show that (3 - Real.sqrt 2)^2 is in the set
      use (3 - Real.sqrt 2), (3 - Real.sqrt 2)
      constructor
      · -- Show the product equals (3 - Real.sqrt 2) ^ 2
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      · -- Show the pair satisfies the circle equation
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    · -- Show that (3 - Real.sqrt 2) ^ 2 is least
      intro t ht
      rcases ht with ⟨x, y, h_eq, h_eq1⟩
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 6), sq_nonneg (x - 3 - (y - 3)), sq_nonneg (x - 3 - Real.sqrt 2), sq_nonneg (y - 3 - Real.sqrt 2), sq_nonneg (x - 3 + Real.sqrt 2), sq_nonneg (y - 3 + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sqrt_nonneg 2, mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]