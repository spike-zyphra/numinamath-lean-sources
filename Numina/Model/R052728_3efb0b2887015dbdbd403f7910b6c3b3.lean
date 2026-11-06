import Mathlib

theorem algebra_244761 {x y : ℝ} (h1 : x^2 - x * y + y^2 = 19) (h2 : x^4 + x^2 * y^2 + y^4 = 931) :
    (x, y) = (-5, -3) ∨ (x, y) = (-3, -5) ∨ (x, y) = (3, 5) ∨ (x, y) = (5, 3) := by

  have h3 : x * y = 15 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x + y), sq_nonneg (x - y)]

  have h4 : x^2 + y^2 = 34 := by
    nlinarith [h1, h3]

  have h5 : (x + y) ^ 2 = 64 := by
    nlinarith [h4, h3]

  have h6 : x + y = 8 ∨ x + y = -8 := by
    have h : (x + y) ^ 2 - 64 = 0 := by linarith
    have factored : (x + y - 8) * (x + y + 8) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp factored) with h8 h8'
    · -- Case $x + y - 8 = 0$
      left
      linarith
    · -- Case $x + y + 8 = 0$
      right
      linarith

  cases h6 with
  | inl h8 =>
    -- In this case, $x + y = 8$ and $x * y = 15$.
    -- Solving quadratic gives $x = 5, y = 3$ or $x = 3, y = 5$
    have h9 : (x - 5) * (x - 3) = 0 := by
      nlinarith [h8, h3]
    cases' (mul_eq_zero.mp h9) with hx5 hx3
    · -- Case $x - 5 = 0$
      have hx : x = 5 := by linarith
      have hy : y = 3 := by linarith [h8, hx]
      simp [hx, hy]
      <;> tauto
    · -- Case $x - 3 = 0$
      have hx : x = 3 := by linarith
      have hy : y = 5 := by linarith [h8, hx]
      simp [hx, hy]
      <;> tauto

  | inr h8 =>
    -- In this case, $x + y = -8$ and $x * y = 15$.
    -- Solving quadratic gives $x = -5, y = -3$ or $x = -3, y = -5$
    have h9 : (x + 5) * (x + 3) = 0 := by
      nlinarith [h8, h3]
    cases' (mul_eq_zero.mp h9) with hx5 hx3
    · -- Case $x + 5 = 0$
      have hx : x = -5 := by linarith
      have hy : y = -3 := by linarith [h8, hx]
      simp [hx, hy]
      <;> tauto
    · -- Case $x + 3 = 0$
      have hx : x = -3 := by linarith
      have hy : y = -5 := by linarith [h8, hx]
      simp [hx, hy]
      <;> tauto