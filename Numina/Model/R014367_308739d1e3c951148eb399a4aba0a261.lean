import Mathlib

theorem algebra_306239 (x y z u : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (hu : u > 0) (h1 : x * z = 3 * u) (h2 : u ^ 2 + y ^ 2 + y * u = x ^ 2) (h3 : y ^ 2 + z ^ 2 - y * z = 9)
    (h4 : x ^ 2 = u ^ 2 + z ^ 2 + 2 * u * z + 9) :
    x = 6 ∧ y = 2 * Real.sqrt 3 ∧ z = Real.sqrt 3 ∧ u = 2 * Real.sqrt 3 := by

  have eq1 : y = 2 * z := by
    nlinarith [sq_nonneg (y - 2 * z), sq_nonneg (z + u), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz, mul_pos hy hu, mul_pos hz hu]

  have eq2 : z ^ 2 = 3 := by
    rw [show y = 2 * z by linarith [eq1]] at h3
    nlinarith [sq_nonneg (z ^ 2 - 3), sq_nonneg (z), mul_pos hz hx, mul_pos hz hy, mul_pos hz hu]

  have eq3 : z = Real.sqrt 3 := by
    have h5 : z ^ 2 = 3 := eq2
    have h6 : z > 0 := hz
    have h7 : z = Real.sqrt 3 := by
      have h8 : z ^ 2 = (3 : ℝ) := h5
      have h9 : z > (0 : ℝ) := h6
      have h10 : z = Real.sqrt 3 := by
        rw [← h8]
        field_simp
      linarith
    linarith

  have eq4 : y = 2 * Real.sqrt 3 := by
    rw [eq3] at eq1
    nlinarith

  have eq5 : x = 6 := by
    have eq6 : z = Real.sqrt 3 := eq3
    have eq7 : x * z = 3 * u := h1
    rw [eq6] at eq7
    have eq8 : u = 2 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - 6), sq_nonneg (u - 2 * Real.sqrt 3)]
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - 6), sq_nonneg (u - 2 * Real.sqrt 3)]

  have eq6 : u = 2 * Real.sqrt 3 := by
    have eq7 : x * z = 3 * u := h1
    rw [eq5, eq3] at eq7
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]

  constructor
  · -- x = 6
    linarith [eq5]
  constructor
  · -- y = 2 * Real.sqrt 3
    linarith [eq4]
  constructor
  · -- z = Real.sqrt 3
    linarith [eq3]
  · -- u = 2 * Real.sqrt 3
    linarith [eq6]