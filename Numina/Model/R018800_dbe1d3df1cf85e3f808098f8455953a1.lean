import Mathlib

theorem algebra_323851 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h1 : x^2 + x * y + y^2 = 25 / 4) (h2 : y^2 + y * z + z^2 = 36)
    (h3 : z^2 + z * x + x^2 = 169 / 4) :
    x * y + y * z + z * x = 10 * Real.sqrt 3 := by
  have h4 : (x * y + y * z + z * x) ^ 2 = 300 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have h5 : x * y + y * z + z * x ≥ 0 := by
    nlinarith
  have h6 : (x * y + y * z + z * x) = Real.sqrt 300 := by
    have h7 : (x * y + y * z + z * x) ^ 2 = (300 : ℝ) := h4
    have h8 : (x * y + y * z + z * x) ≥ 0 := h5
    have h9 : (x * y + y * z + z * x) = Real.sqrt 300 := by
      rw [← h7]
      field_simp [Real.sqrt_sq_eq_abs, abs_of_nonneg h8]
    exact h9
  have h8 : Real.sqrt 300 = 10 * Real.sqrt 3 := by
    calc
      Real.sqrt 300 = Real.sqrt (10 ^ 2 * (3 : ℝ)) := by
        norm_num
        <;> ring_nf <;> norm_num
      _ = (10 : ℝ) * Real.sqrt (3 : ℝ) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
        <;> ring_nf <;> norm_num
      _ = (10 * Real.sqrt 3 : ℝ) := by ring
  rw [h8] at h6
  nlinarith