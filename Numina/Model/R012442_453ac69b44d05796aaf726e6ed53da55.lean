import Mathlib

open Real

theorem inequalities_597644 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x^2 + y^2 + z^2 = 1) :
    x * y / z + y * z / x + z * x / y ≥ sqrt 3 := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have eq : x * y / z + y * z / x + z * x / y = (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) / (x * y * z) := by
    field_simp
    ring
  have h2 : sqrt 3 ≥ 0 := by positivity
  have h3 : (x * y / z + y * z / x + z * x / y) ^ 2 ≥ 3 := by
    have eq1 : (x * y / z + y * z / x + z * x / y) ^ 2 = (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ^ 2 / (x * y * z) ^ 2 := by
      have eq2 : x * y / z + y * z / x + z * x / y = (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) / (x * y * z) := by
        field_simp
        ring
      rw [eq2]
      <;> field_simp
      <;> ring_nf
    rw [eq1]
    have h7 : (x * y * z) ^ 2 > 0 := by positivity
    have h8 : (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ^ 2 ≥ 3 * (x * y * z) ^ 2 := by
      nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        sq_nonneg (x^2 * y^2 - y^2 * z^2), sq_nonneg (y^2 * z^2 - z^2 * x^2), sq_nonneg (z^2 * x^2 - x^2 * y^2),
        mul_pos hx hy, mul_pos hy hz, mul_pos hx hz
      ]
    have h9 : (x^2 * y^2 + y^2 * z^2 + z^2 * x^2) ^ 2 / (x * y * z) ^ 2 ≥ 3 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    exact h9
  have h4 : (x * y / z + y * z / x + z * x / y) ≥ 0 := by positivity
  have h5 : sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) ≥ sqrt (3 : ℝ) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have h6 : sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) = (x * y / z + y * z / x + z * x / y) := by
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg h4]
  have h8 : (x * y / z + y * z / x + z * x / y) ≥ sqrt (3 : ℝ) := by
    have h5 : sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) ≥ sqrt (3 : ℝ) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    have h6 : sqrt ((x * y / z + y * z / x + z * x / y) ^ 2) = (x * y / z + y * z / x + z * x / y) := by
      rw [Real.sqrt_sq_eq_abs]
      rw [abs_of_nonneg h4]
    linarith [h6, h5]
  exact h8