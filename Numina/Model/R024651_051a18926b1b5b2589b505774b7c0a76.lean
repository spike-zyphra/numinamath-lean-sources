import Mathlib

theorem inequalities_155518 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x / y + y / z + z / x) / 3 ≥ 1 ∧
    x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 ≥ ((x / y + y / z + z / x) ^ 2) / 3 ∧
    x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 ≥ x / y + y / z + z / x := by
  -- First inequality: Use the AM-QM inequality
  have h1 : (x / y + y / z + z / x) / 3 ≥ 1 := by
    have h21 : 0 < x * y * z := mul_pos (mul_pos hx hy) hz
    have h22 : x / y + y / z + z / x - 3 ≥ 0 := by
      have h23 : x / y + y / z + z / x - 3 = (x^2 * z + y^2 * x + z^2 * y - 3 * x * y * z) / (x * y * z) := by
        field_simp
        ring
      rw [h23]
      have h24 : x^2 * z + y^2 * x + z^2 * y - 3 * x * y * z ≥ 0 := by
        nlinarith [sq_nonneg (x * z - y * x), sq_nonneg (y * x - z * y), sq_nonneg (z * y - x * z),
            sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
            mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
      apply div_nonneg h24 (by positivity)
    linarith
  -- Second inequality: Use Cauchy-Schwarz
  have h2 : x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 ≥ ((x / y + y / z + z / x) ^ 2) / 3 := by
    have h66 : x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 - ((x / y + y / z + z / x) ^ 2) / 3 ≥ 0 := by
      have h67 : x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 - ((x / y + y / z + z / x) ^ 2) / 3 =
          (3 * (x^4 * z^2 + y^4 * x^2 + z^4 * y^2) - (x / y + y / z + z / x) ^ 2 * (x * y * z)^2) / (3 * (x * y * z) ^ 2) := by
        field_simp
        ring_nf
        <;> field_simp
        <;> ring
      rw [h67]
      have h41 : (x * y * z) ^ 2 > 0 := by positivity
      have h50 : 3 * (x^4 * z^2 + y^4 * x^2 + z^4 * y^2) - (x / y + y / z + z / x) ^ 2 * (x * y * z) ^ 2 ≥ 0 := by
        have h48 : (x / y + y / z + z / x) = (x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) / (x * y * z) := by
          field_simp
          <;> ring_nf
          <;> field_simp
          <;> ring
        rw [h48] at *
        have h24 : (x * y * z)^2 > 0 := by positivity
        have h49 : 3 * (x^4 * z^2 + y^4 * x^2 + z^4 * y^2) - ((x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) / (x * y * z) ) ^ 2 * (x * y * z) ^ 2 ≥ 0 := by
          have h50 : ((x ^ 2 * z + y ^ 2 * x + z ^ 2 * y) / (x * y * z) ) ^ 2 * (x * y * z)^2 = (x^2 * z + y^2 * x + z^2 * y) ^ 2 := by
            field_simp
            <;> ring_nf
            <;> field_simp
          rw [h50]
          nlinarith [sq_nonneg (x^2 * z - y^2 * x), sq_nonneg (y^2 * x - z^2 * y), sq_nonneg (z^2 * y - x^2 * z),
              sq_nonneg (x / y * z - y / z * x), sq_nonneg (y / z * (x - z)), sq_nonneg (z / x * (x - z)),
              sq_nonneg (x * (x - y)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), 
              mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
        nlinarith
      apply div_nonneg h50 (by positivity)
    linarith
  -- Third inequality: Use the first two parts
  have h3 : x ^ 2 / y ^ 2 + y ^ 2 / z ^ 2 + z ^ 2 / x ^ 2 ≥ x / y + y / z + z / x := by
    nlinarith [h1, h2, sq_nonneg (x / y - 1), sq_nonneg (y / z - 1), sq_nonneg (z / x - 1), mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  constructor
  · exact h1
  constructor
  · exact h2
  · exact h3
  <;> nlinarith
  <;> nlinarith
  <;> nlinarith
  <;> all_goals linarith