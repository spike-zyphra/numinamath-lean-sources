import Mathlib

theorem algebra_132855 {x y : ℝ} (h1 : x + y^2 = x * y + 1) (h2 : x * y = 4 + y) :
    (x, y) = (5, 1) ∨ (x, y) = (3, 2) ∨ (x, y) = (-1, -2) := by
  have eq3 : x = 5 + y - y^2 := by
    nlinarith [h2]

  -- Substituting into the second equation
  have eq4 : (5 + y - y^2) * y = 4 + y := by 
    rw [eq3] at h2
    linarith

  have h3 : (y - 1) * (y - 2) * (y + 2) = 0 := by
    nlinarith [sq_nonneg (y - 2), sq_nonneg (y + 2), sq_nonneg (x - 5 : ℝ), sq_nonneg (x - 3 : ℝ), sq_nonneg (x + 1 : ℝ)]

  cases' (mul_eq_zero.mp h3) with h3_a h3_b
  cases' (mul_eq_zero.mp h3_a) with h3_a1 h3_a2
  · -- Solve for $y$ and then compute $x$ from $y$
    have hy : y = 1 := by linarith
    have hx : x = 5 := by 
      rw [hy] at eq3
      nlinarith
    left
    exact Prod.ext hx hy

  · -- Now solving for y:
    have hy : y = 2 := by linarith
    have hx : x = 3 := by 
      rw [hy] at eq3
      nlinarith
    right
    left
    exact Prod.ext hx hy

  · -- Solving for $y$:
    have hy : y = -2 := by linarith
    have hx : x = -1 := by 
      rw [hy] at eq3
      nlinarith
    right
    right
    exact Prod.ext hx hy