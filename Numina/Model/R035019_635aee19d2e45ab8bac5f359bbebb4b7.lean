import Mathlib

theorem inequalities_62701 (x y z : ℝ) (hx : x ≥ 1 / 2) (hy : y ≥ 1 / 2) (hz : z ≥ 1 / 2)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    ((1 / x + 1 / y - 1 / z) * (1 / x - 1 / y + 1 / z)) ≥ 2 := by
  have hx1 : x ≠ 0 := by linarith
  have hy1 : y ≠ 0 := by linarith
  have hz1 : z ≠ 0 := by linarith
  have hx2 : 0 < x := by linarith
  have hy2 : 0 < y := by linarith
  have hz2 : 0 < z := by linarith
  have h11 : ((1 / x + 1 / y - 1 / z) * (1 / x - 1 / y + 1 / z)) =
      (1 / x^2) - (1 / y^2) - (1 / z^2) + 2 / (y * z) := by
    field_simp
    ring
  rw [h11]
  have h44 : (1 / x^2) - (1 / y^2) - (1 / z^2) + 2 / (y * z) - 2 ≥ 0 := by
    have h55 : (1 / x^2) - (1 / y^2) - (1 / z^2) + 2 / (y * z) - 2 =
          (y ^ 2 * z ^ 2 - x^2 * z^2 - x^2 * y^2 + 2 * x ^ 2 * y * z - 2 * (x^2 * y ^ 2 * z ^ 2 )) / (x^2 * y^2 * z^2) := by 
      field_simp
      ring
    rw [h55] at *
    have h23 : x^2 * y^2 * z^2 > 0 := by 
      positivity
    have h33 : y ^ 2 * z ^ 2 - x^2 * z^2 - x^2 * y^2 + 2 * x ^ 2 * y * z - 2 * (x^2 * y ^ 2 * z ^ 2 ) ≥ 0 := by 
      have hx22 : x^2 ≥ 1/4 := by nlinarith
      have hy22 : y^2 ≥ 1/4 := by nlinarith
      have hz22 : z^2 ≥ 1/4 := by nlinarith
      -- Substitute x^2 based on h
      have h77 : x^2 = 1 - y^2 - z^2 := by 
        nlinarith
      rw [h77]
      -- Now it's an inequality in terms of y and z.
      -- Replace with known methods.
      nlinarith [sq_nonneg (y^2 - z^2), sq_nonneg (y * z - 1 / 2), sq_nonneg (y - z),
          mul_nonneg (show (0 : ℝ) ≤ y - 1 / 2 by linarith) (show (0 : ℝ) ≤ z - 1 / 2 by linarith), 
          sq_nonneg ((1 : ℝ) - y^2 - z^2 - 1/4), 
          mul_nonneg (show (0 : ℝ) ≤ y^2 - 1/4 by nlinarith) (show (0 : ℝ) ≤ z^2 - 1/4 by nlinarith)
      ]
    apply div_nonneg 
    linarith 
    positivity
  linarith
  all_goals nlinarith