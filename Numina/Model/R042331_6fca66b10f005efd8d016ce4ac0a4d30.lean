import Mathlib

open Real

theorem inequalities_599779 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    x * y / z + y * z / x + z * x / y ≥ sqrt 3 ∧
    ∃ x y z : ℝ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 + y^2 + z^2 = 1 ∧
    x * y / z + y * z / x + z * x / y = sqrt 3 := by
  have h1 : x * y / z + y * z / x + z * x / y ≥ sqrt 3 := by
    have h2 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
      have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 =
          (x * y / z)^2 + (y * z / x)^2 + (z * x / y)^2 + 2 * (x * y / z * (y * z / x) + x * y / z * (z * x / y) + (y * z / x) * (z * x / y)) := by ring
      have h4 : x * y / z * (y * z / x) = y ^ 2 := by
        field_simp [show 0 < x by linarith, show 0 < y by linarith, show 0 < z by linarith]
        <;> ring
      have h5 : x * y / z * (z * x / y) = x ^ 2 := by
        field_simp [show 0 < x by linarith, show 0 < y by linarith, show 0 < z by linarith]
        <;> ring
      have h6 : (y * z / x) * (z * x / y) = z ^ 2 := by
        field_simp [show 0 < x by linarith, show 0 < y by linarith, show 0 < z by linarith]
        <;> ring
      rw [h3, h4, h5, h6]
      nlinarith [ sq_nonneg (x * y / z - y * z / x), sq_nonneg (y * z / x - z * x / y), sq_nonneg (z * x / y - x * y / z), sq_nonneg (x^2 + y^2 + z^2 - 1), h, mul_pos hx hy, mul_pos hx hz, mul_pos hy hz ]
    have h3 : sqrt 3 ≥ 0 := by positivity
    have h4 : (x * y / z + y * z / x + z * x / y) ≥ 0 := by positivity
    have h5 : (x * y / z + y * z / x + z * x / y) ≥ sqrt 3 := by
      have h6 : sqrt 3 ≥ 0 := by positivity
      have h7 : (x * y / z + y * z / x + z * x / y) ≥ 0 := by positivity
      have h8 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := h2
      have h9 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ (sqrt 3) ^ 2 := by
        nlinarith [ h8, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
      nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
    exact h5
  constructor
  · exact h1
  · -- Show existence of-points
    use Real.sqrt (1 / 3), Real.sqrt (1 / 3), Real.sqrt (1 / 3)
    constructor
    · -- Show positivity of sqrt (1 / 3)
      positivity
    constructor
    · -- Show positivity of sqrt (1 / 3)
      positivity
    constructor
    · -- Show positivity of sqrt (1 / 3)
      positivity
    constructor
    · -- Show the point satisifes the constraint
      have h4 : Real.sqrt (1 / 3)^2 + Real.sqrt (1 / 3)^2 + Real.sqrt (1 / 3) ^ 2 = 1 := by
        have h11 : Real.sqrt (1 / 3) ^ 2 = (1 / 3 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        nlinarith [h11]
      linarith [h4]
    · -- Show the point satisifes the equality
      have h4 : Real.sqrt (1 / 3) ^ 2 = (1 / 3 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h8 : Real.sqrt (1 / 3) * Real.sqrt (1 / 3) = (1 / 3 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (1 / 3), h4]
      field_simp [show 0 < Real.sqrt (1 / 3) by positivity, Real.sqrt_nonneg (1 / 3), h4, h8]
      <;> nlinarith [Real.sqrt_nonneg (1 / 3), h4, h8, Real.sq_sqrt (show (0 : ℝ) ≤ (1 / 3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num) ]
      all_goals linarith