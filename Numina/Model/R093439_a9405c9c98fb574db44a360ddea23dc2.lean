import Mathlib

theorem algebra_20439 (x : ℝ) (hx : x^2 - 5 * x - 36 = 0) :
    x ≤ 9 ∧ (∃ x, x^2 - 5 * x - 36 = 0 ∧ x = 9) := by 
  have h1 : (x - 9) * (x + 4) = 0 := by
    linarith [hx]
  cases' (mul_eq_zero.1 h1) with h2 h3 
  · -- Case where $x - 9 = 0$, which implies $x = 9$
    constructor 
    · -- Show $x ≤ 9$
      linarith 
    · -- Show existence of $x$ such that $x^2 - 5 x - 36 = 0$ and $x = 9$
      use 9 
      constructor 
      · -- Show $9^2 - 5 * 9 - 36 = 0$
        norm_num 
      · -- Show $9 = 9$
        rfl 
  · -- Case where $x + 4 = 0$, which implies $x = -4$
    constructor 
    · -- Show $x ≤ 9$
      linarith 
    · -- Show existence of $x$ such that $x^2 - 5 x - 36 = 0$ and $x = 9$
      use 9 
      constructor 
      · -- Show $9^2 - 5 * 9 - 36 = 0$
        norm_num 
      · -- Show $9 = 9$
        rfl