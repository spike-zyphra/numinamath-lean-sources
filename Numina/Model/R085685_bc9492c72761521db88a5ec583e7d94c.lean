import Mathlib

theorem algebra_163449 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : x + 1 / y = 10) (h2 : y + 1 / x = 5 / 12) :
    x = 4 ∨ x = 6 := by
  have eq1 : x * y + 1 = 10 * y := by
    field_simp [hy] at h1
    linarith
  have eq2 : x * y + 1 = (5 / 12) * x := by
    field_simp [hx] at h2
    linarith
  -- From eq1 and eq2: 10 * y = (5 / 12) * x
  have eq3 : 10 * y = (5 / 12) * x := by
    linarith [eq1, eq2]
  -- Solving for y from eq3
  have eq4 : y = (1 / 24) * x := by
    linarith
  -- Substituting y = (1 / 24) * x into eq1
  rw [eq4] at eq1
  -- This yields the quadratic equation
  have eq5 : x^2 - 10 * x + 24 = 0 := by
    nlinarith
  -- Factor the quadratic equation
  have eq6 : (x - 4) * (x - 6) = 0 := by
    nlinarith [eq5]
  cases' (mul_eq_zero.1 eq6) with h3 h4
  · -- Case 1: x - 4 = 0
    left
    linarith
  · -- Case 2: x - 6 = 0
    right
    linarith