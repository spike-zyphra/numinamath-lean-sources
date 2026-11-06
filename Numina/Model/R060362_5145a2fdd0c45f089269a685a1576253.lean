import Mathlib

theorem inequalities_187549 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    4 / (x + y) ≤ 1 / x + 1 / y := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : 0 < x + y := add_pos hx hy
  
  have h3 : 4 * x * y ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (x - y)]
  
  have h4 : 4 / (x + y) ≤ 1 / x + 1 / y := by
    have h5 : 0 < x * y * (x + y) := by
      apply mul_pos
      apply mul_pos
      all_goals linarith

    have h6 : 4 * x * y ≤ (x + y) ^ 2 := by 
      nlinarith [sq_nonneg (x - y)]

    have h7 : 4 / (x + y) - (1 / x + 1 / y) ≤ 0 := by
      have h8 : 4 / (x + y) - (1 / x + 1 / y) = (4 * x * y - (x + y) ^ 2) / (x * y * (x + y)) := by
        field_simp
        <;> ring
      rw [h8]

      -- We have $4xy - (x + y)^2 \leq 0$ and denominator $x * y * (x + y) > 0$.
      have h9 : 4 * x * y - (x + y) ^ 2 ≤ 0 := by nlinarith

      have h10 : 0 ≤ x * y * (x + y) := by positivity

      apply div_nonpos_of_nonpos_of_nonneg h9 (by positivity)
    
    linarith

  exact h4