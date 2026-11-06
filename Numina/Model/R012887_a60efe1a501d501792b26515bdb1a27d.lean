import Mathlib

theorem algebra_130356 {x a : ℝ} (hx : x ≠ -2) (ha : a = -3 * x ^ 2 + 5 * x - 2)
    (h : a = 4 * (x ^ 2 - 1) / (x + 2)) :
    x * (x - 1) * (3 * x + 8) = 0 := by
  have eq1 : x + 2 ≠ 0 := by
    intro h1
    apply hx
    linarith
  have eq2 : a = 4 * (x ^ 2 - 1) / (x + 2) := h
  rw [ha] at eq2
  have eq3 : (-3 * x ^ 2 + 5 * x - 2) * (x + 2) = 4 * (x ^ 2 - 1) := by
    have eq4 : x + 2 ≠ 0 := eq1
    field_simp [eq4] at eq2 ⊢
    linarith
  -- Now we have the equation without fractions. Let's expand both sides.
  -- We need to show x * (x - 1) * (3 * x + 8) = 0 from eq3
  -- Let's compute left side of eq3:
  -- (-3 * x ^ 2 + 5 * x - 2) * (x + 2)
  -- = (-3 * x ^ 2) * x + (-3 * x ^ 2) * 2 + (5 * x) * x + (5 * x) * 2 + (-2) * x + (-2) * 2
  -- = -3 * x ^ 3 -6 * x ^ 2 +5 * x ^2 +10 * x -2 * x -4
  -- = -3 * x ^3 + (-6 *x^2 +5 * x^2) + (10 * x -2 *x) -4
  -- = -3 *x^3 -x^2 +8 *x -4
  -- Right side:
  -- 4 * (x ^ 2 -1)
  -- = 4 *x^2 -4
  -- Equation:
  -- -3 *x^3 -x^2 +8 *x -4 =4 *x^2 -4
  -- Bring all terms to left side:
  -- -3 *x^3 -x^2 +8 * x -4 -4 *x^2 +4=0
  -- -3 *x^3 -5 *x^2 +8 *x =0
  -- Factor:
  -- x (-3 *x^2 -5 *x +8 )=0
  -- x (x -1)(3x +8 )=0
  -- This should be equal to x * (x -1) * (3x +8 ) =0.
  -- Let's do the manipulation.
  have eq5 : x * (x - 1) * (3 * x + 8) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show x + 2 ≠ 0 by exact eq1)]
  exact_mod_cast eq5