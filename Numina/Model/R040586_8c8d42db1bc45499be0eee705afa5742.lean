import Mathlib

theorem algebra_166099 (x y : ℝ) :
    (x^2 + y^2 - 2 * x + 3 * y - 9 = 0 ∧ 2 * x^2 + 2 * y^2 + x - 5 * y - 1 = 0) ↔
    (x = -239 / 146 ∧ y = 117 / 146) ∨ (x = 1 ∧ y = 2) := by
  constructor
  · -- Forward direction: if (x, y) satisfies both equations, then it's one of the two solutions
    intro h
    rcases h with ⟨h₁, h₂⟩
    -- Subtract the second equation from twice the first equation multiplied by 2
    -- We multiply the first equation by 2: 2x² + 2y² - 4x + 6 y - 18 = 0
    -- Then subtract the second equation: 2x² + 2y² + x -5y -1 = 0
    -- The result is: -5x + 11y - 17 = 0
    have h3 : 5 * x - 11 * y + 17 = 0 := by
      nlinarith 
    -- Solving the linear equation for x: 5x =11y -17
    -- Therefore x = (11y -17)/5
    have h4 : x = (11 * y - 17) / 5 := by 
      linarith
    -- Substitute this expression for x into the first equation
    -- First, substitute into first equation: x^2+y^2-2x+3y -9 =0
    -- We get: ((11y -17)/5) ^2 + y^2 -2 * ((11y -17)/5) + 3 y -9 =0
    have h1' : ((11 * y - 17) / 5) ^ 2 + y ^ 2 - 2 * ((11 * y - 17) / 5) + 3 * y - 9 = 0 := by
      rw [show x = (11 * y - 17) / 5 by linarith [h4]] at h₁ 
      linarith
    -- Now, clear denominators by multiplying through by 25 = 5²
    have h5 : 146 * y ^ 2 - 409 * y + 234 = 0 := by 
      nlinarith [h1']
    -- Now, factor the quadratic to get two possibilities for y
    have h6 : (y - 117 / 146) * (y - 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Case where y = 117/146, then x = -239/146.
      have hy : y = 117 / 146 := by
        linarith
      have hx : x = -239 / 146 := by
        linarith [h3, hy]
      left
      exact ⟨hx, hy⟩
    · -- Case where y = 2, then x = 1.
      have hy : y = (2 : ℝ) := by 
        linarith 
      have hx : x = (1 : ℝ) := by 
        nlinarith [h3, hy]
      right
      exact ⟨hx, hy⟩
  · -- Backward direction: if (x, y) is either of the solutions, then both equations are satisfied
    rintro (h | h)
    · -- First solution
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check the first equation
        norm_num
      · -- Check the second equation
        norm_num
    · -- Second solution
      rcases h with ⟨rfl, rfl⟩
      constructor
      · -- Check the first equation
        norm_num
      · -- Check the second equation
        norm_num