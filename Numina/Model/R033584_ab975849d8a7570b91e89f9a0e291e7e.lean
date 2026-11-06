import Mathlib

open Real

theorem inequalities_275708 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    y * z / x + x * z / y + x * y / z ≥ sqrt 3 ∧
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 + y^2 + z^2 = 1 ∧
      y * z / x + x * z / y + x * y / z = sqrt 3 := by
  -- We need to prove both parts:
  -- 1. The inequality $y * z / x + x * z / y + x * y / z \geq \sqrt{3}$
  -- 2. The existence of $x, y, z$ such that the equality holds
  have h1 : 0 < x * y * z := by
    positivity
  -- Now we have that the square of the expression is ≥3, so the expression is ≥sqrt(3).
  have h2 : (y * z / x + x * z / y + x * y / z) ^2 ≥ 3 := by
    have h3 : (y * z / x + x * z / y + x * y / z) ^2 = (y * z / x) ^2 + (x * z / y) ^2 + (x * y / z) ^2 + 2 * ( (y * z / x) * (x * z / y) + (y * z / x) * (x * y / z) + (x * z / y) * (x * y / z) ) := by ring
    rw [h3]
    have h4 : (y * z / x) * (x * z / y) = z^2 := by
      field_simp
      ring
    have h5 : (y * z / x) * (x * y / z) = y^2 := by
      field_simp
      ring
    have h6 : (x * z / y) * (x * y / z) = x^2 := by
      field_simp
      ring
    rw [h4, h5, h6]
    nlinarith [sq_nonneg (y * z / x - x * z / y), sq_nonneg (y * z / x - x * y / z), sq_nonneg (x * z / y - x * y / z),
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  -- Now, we can extract the inequality with sqrt.
  have h3_0 : y * z / x + x * z / y + x * y / z ≥ sqrt 3 := by
    have h4_0 : sqrt 3 ≥ 0 := by positivity
    have h5_0 : (y * z / x + x * z / y + x * y / z) ≥ 0 := by positivity
    have h6_0 : (sqrt 3) ^2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    nlinarith [show sqrt 3 ≥ 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h2]
  have h4_0 : ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 + y^2 + z^2 = 1 ∧
      y * z / x + x * z / y + x * y / z = sqrt 3 := by
    use Real.sqrt 3 / 3, Real.sqrt 3 / 3, Real.sqrt 3 / 3
    constructor
    · -- Show that sqrt 3 / 3 > 0
      positivity
    constructor
    · -- Show that sqrt 3 / 3 > 0
      positivity
    constructor
    · -- Show that sqrt 3 / 3 > 0
      positivity
    constructor
    · -- Show that (sqrt 3 / 3)^2 + ... = 1
      have h10 : Real.sqrt 3 ^2 = 3 := by
        exact Real.sq_sqrt (by norm_num)
      nlinarith
    · -- Show the equality of the expression
      have h11 : Real.sqrt 3 ^2 = 3 := by
        exact Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < (3 : ℝ)), Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]
  -- The goal has two parts connected by ∧, so we need to split the conjunction.
  constructor
  · exact h3_0
  · exact h4_0