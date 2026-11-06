import Mathlib

/- Let $x, y$ be positive real numbers such that $x^{3}+y^{3} \leq x^{2}+y^{2}$. Find the greatest possible value of the product $x y$. -/
theorem inequalities_605796 :
  IsGreatest {x * y | (x : ℝ) (y : ℝ) (_ : x > 0) (_ : y > 0) (_ : x ^ 3 + y ^ 3 ≤ x ^ 2 + y ^ 2)} 1 := by
  -- First, we show that 1 can be attained.
  constructor
  . -- When x = y = 1, the conditions are satisfied and the product is 1.
    use 1, 1
    simp
  . -- Let x, y be positive real numbers such that x ^ 3 + y ^ 3 ≤ x ^ 2 + y ^ 2.
    rintro z ⟨x, y, hx, hy, h, rfl⟩
    -- We show that x * y ≤ 1.

    have h₁ : (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2) ≤ (x + y) * (x ^ 2 + y ^ 2) := by
      calc
        -- (x ^ 2 + y ^ 2) * (x ^ 2 + y ^ 2) ≤ (x + y) * (x ^ 3 + y ^ 3), because RHS - LHS is x * y * (x - y) ^ 2 ≥ 0.
        _ ≤ (x + y) * (x ^ 3 + y ^ 3) := by
          linarith only [show x * y * (x - y) ^ 2 ≥ 0 by positivity]
        -- (x + y) * (x ^ 2 + y ^ 2) ≤ (x + y) * (x ^ 2 + y ^ 2) from the hypothesis.
        _ ≤ (x + y) * (x ^ 2 + y ^ 2) := by
          rwa [mul_le_mul_left (by positivity)]
    -- Cancel the (x + y) on both sides, and we get x ^ 2 + y ^ 2 ≤ x + y.
    rw [mul_le_mul_right (by positivity)] at h₁

    have h₂ : (x + y) * (x + y) ≤ 2 * (x + y) := by
      calc
        -- (x + y) * (x + y) ≤ 2 * (x ^ 2 + y ^ 2), because RHS - LHS is (x - y) ^ 2 ≥ 0.
        _ ≤ 2 * (x ^ 2 + y ^ 2) := by
          linarith only [show (x - y) ^ 2 ≥ 0 by positivity]
        -- 2 * (x ^ 2 + y ^ 2) ≤ 2 * (x + y) from the lemma
        _ ≤ 2 * (x + y) := by
          linarith only [h₁]
    -- Cancel the (x + y) on both sides, and we get x + y ≤ 2.
    rw [mul_le_mul_right (by positivity)] at h₂
    -- Now x * y ≤ (x + y) ^ 2 / 4 ≤ 1.
    calc
      x * y ≤ (x + y) ^ 2 / 4 := by
        linarith only [show (x - y) ^ 2 ≥ 0 by positivity]
      _ ≤ 1 := by
        nlinarith only [h₂, show x + y > 0 by positivity]
