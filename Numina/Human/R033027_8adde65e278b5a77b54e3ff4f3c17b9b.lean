import Mathlib
/- Let $x, y$, and $z$ be positive real numbers such that $(x \cdot y)+z=(x+z) \cdot(y+z)$. What is the maximum possible value of $x y z$ ? -/
theorem algebra_611353 : IsGreatest {a : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ a = x * y * z ∧ x * y + z = (x + z) * (y + z)} (1 / 27):= by
  -- Prove that 1/27 is in the set
  constructor
  .
    -- Simplify and use x = 1/3
    simp
    use (1 / 3)
    -- Simplify and use y = 1/3
    simp
    use (1 / 3)
    -- Simplify and use z = 1/3
    simp
    use (1 / 3)
    simp
    norm_num
  -- Prove that 1/27 is an upper bound
  .
    simp [upperBounds]
    intro a x hx y hy z hz ha h
    subst ha
    -- Show that z*(x+y+z-1) = 0
    replace h : z * (x + y + z - 1) = 0:= by linarith
    -- Prove z ≠ 0 using positivity
    have hz1 : z ≠ 0:= by linarith
    simp [hz1] at h
    -- Deduce that x + y + z = 1
    replace h : x + y + z = 1:= by linarith
    field_simp
    -- Use AM-GM inequality: x* y*z ≤ ((x+y+z)/3)^3
    suffices x * y * z ≤ ((x + y + z) / 3) ^ 3 by rw [h] at this ; linarith
    -- Use non-negativity of quadratic expressions
    have h1 : x * (y - z) ^ 2 + y * (z - x) ^ 2 + z * (x - y) ^ 2 ≥ 0:= by positivity
    have h2 : (y + z) * (y - z) ^ 2 + (z + x) * (z - x) ^ 2 + (x + y) * (x - y) ^ 2 ≥ 0:= by positivity
    linarith
