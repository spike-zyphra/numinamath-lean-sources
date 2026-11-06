import Mathlib

theorem algebra_22 (x : ℝ) (hx : x ≠ 3) (hx1 : x ≠ 0) : (x - 3) / x - 1 = 2 / (x - 3) ↔ x = 9 / 5 := by
  constructor
  · -- Assume (x - 3) / x - 1 = 2 / (x - 3) prove x = 9 / 5
    intro h
    have h1 : x - 3 ≠ 0 := by 
      intro h2 
      apply hx 
      linarith 
    have h2 : x ≠ 0 := hx1
    have eq1 : (x - 3) / x - 1 = 2 / (x - 3) := h 
    have eq2 : (x - 3) ^ 2 - x * (x - 3) = 2 * x := by 
      have denom1 : x ≠ 0 := h2 
      have denom2 : x - 3 ≠ 0 := h1 
      field_simp [denom1, denom2] at eq1 ⊢ 
      nlinarith 
    -- Simplify the left side
    have eq3 : (x - 3) ^ 2 - x * (x - 3) = -3 * x + 9 := by
      nlinarith 
    rw [eq3] at eq2 
    -- Solving the equation gives us
    linarith 
  · -- Assume x = 9/5 prove (x - 3) / x -1 = 2/(x - 3)
    intro h 
    rw [h] 
    norm_num