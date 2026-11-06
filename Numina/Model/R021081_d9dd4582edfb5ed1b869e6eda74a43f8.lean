import Mathlib

open Real

theorem inequalities_208061 :
    IsLeast {t : ℝ | ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^2 + y^2 + z^2 = 1 ∧ t = x * y / z + y * z / x + z * x / y} (Real.sqrt 3) := by
  constructor
  · -- Show that sqrt(3) is in the set.
    use 1 / Real.sqrt 3, 1 / Real.sqrt 3, 1 / Real.sqrt 3
    constructor
    · -- Show x > 0
      positivity
    constructor
    · -- Show y > 0
      positivity
    constructor
    · -- Show z > 0
      positivity
    constructor
    · -- Show x^2 + y^2 + z^2 = 1
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
    · -- Show t = x * y / z + y * z / x + z * x / y
      have h1 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      field_simp [h1]
      <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)]
  · -- Show that sqrt(3) is the least
    intro t ht
    rcases ht with ⟨x, y, z, hx, hy, hz, h1, heq⟩
    have h2 : x * y / z + y * z / x + z * x / y ≥ Real.sqrt 3 := by
      have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
        have h4 : (x * y / z + y * z / x + z * x / y) ^ 2 =
            (x * y / z)^2 + (y * z / x)^2 + (z * x / y)^2 + 2 * ((x * y / z) * (y * z / x) + (x * y / z) * (z * x / y) + (y * z / x) * (z * x / y)) := by
          ring
        rw [h4]
        have h5 : (x * y / z) * (y * z / x) = y ^ 2 := by
          field_simp
          <;> ring
        have h6 : (x * y / z) * (z * x / y) = x ^ 2 := by
          field_simp
          <;> ring
        have h7 : (y * z / x) * (z * x / y) = z ^ 2 := by
          field_simp
          <;> ring
        rw [h5, h6, h7]
        nlinarith [sq_nonneg (x * y / z - y * z / x), sq_nonneg (x * y / z - z * x / y), sq_nonneg (y * z / x - z * x / y), 
          sq_nonneg (x^2 + y^2 + z^2 - 1), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]
      have h4 : (x * y / z + y * z / x + z * x / y) ≥ 0 := by
        positivity
      have h5 : Real.sqrt 3 ≥ 0 := by positivity
      have h7 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg 3, h7]
    linarith [h2, heq]