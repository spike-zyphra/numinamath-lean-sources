import Mathlib

theorem algebra_199707 {a b : ℝ} {x y : ℝ} (ha : a = 5 / 10) (hb : b = 3 / 10)
    (hxy : x / a + y / b = 90)
    (h' : x + y = 35) :
    x = 20 ∧ y = 15 := by
  rw [ha, hb] at hxy
  constructor
  · -- Solving the equation system:
    -- x / (0.5) + y / (0.3) = 90
    -- x + y = 35
    -- This converts to:
    -- 2 * x + (10 / 3) * y = 90
    -- x + y = 35
    -- Substituting x = 35 - y
    -- 2 * (35 - y) + (10 / 3) * y = 90
    -- (70) - 2 * y + (10 / 3) * y = 90
    -- (8 / 3) * y = -20
    -- Multiplication by 3: 8 * y = -60
    -- y = -7.5
    -- This system is inconsistent, as that doesn't match.
    field_simp at hxy
    linarith
  · -- From total vatrushki and solved time.
    field_simp at hxy
    linarith