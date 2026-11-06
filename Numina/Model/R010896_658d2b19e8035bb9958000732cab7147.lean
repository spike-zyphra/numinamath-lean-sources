import Mathlib

theorem inequalities_201318 (x : ℝ) :
    Real.sqrt (3 * x^2 + 2 * x + 1) + Real.sqrt (3 * x^2 - 4 * x + 2) ≥
    Real.sqrt 51 / 3 := by 
  set y := Real.sqrt (3 * x^2 + 2 * x + 1)
  set z := Real.sqrt (3 * x^2 - 4 * x + 2)
  have hy2 : y^2 = 3 * x^2 + 2 * x + 1 := by
    rw [Real.sq_sqrt]
    nlinarith [sq_nonneg (x + 1 / 3)]
  have hz2 : z^2 = 3 * x^2 - 4 * x + 2 := by 
    rw [Real.sq_sqrt]
    nlinarith [sq_nonneg (x - 2 / 3)]
  have hy4_pos : 0 ≤ (3 * x^2 + 2 * x + 1 : ℝ) := by 
    nlinarith [sq_nonneg (x * 3 + 1)]
  have hz4_pos : 0 ≤ (3 * x^2 - 4 * x + 2 : ℝ) := by
    nlinarith [sq_nonneg (x * 3 - 2)]
  have h11 : (Real.sqrt 51 / 3) ^ 2 = (51 / 9 : ℝ) := by
    calc
      (Real.sqrt 51 / 3) ^ 2 = (Real.sqrt 51) ^ 2 / 9 := by ring
      _ = (51 / 9 : ℝ) := by 
        rw [Real.sq_sqrt (by norm_num)]
        <;> ring
  have h50 : (y + z) ^ 2 ≥ (Real.sqrt 51 / 3) ^ 2 := by
    nlinarith [sq_nonneg (y - z), sq_nonneg (x - 2 / 3), sq_nonneg (x + 1 / 3),
      h11, Real.sqrt_nonneg 51, Real.sq_sqrt (show 0 ≤ (51 : ℝ) by norm_num), 
      mul_nonneg (Real.sqrt_nonneg (3 * x^2 + 2 * x + 1)) (Real.sqrt_nonneg (3 * x^2 - 4 * x + 2)), 
      sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (y * z - Real.sqrt ((3 * x^2 + 2 * x + 1) * (3 * x^2 - 4 * x + 2)))
      ]
  have h51 : (y + z) ≥ 0 := by positivity
  have h54 : (Real.sqrt 51 / 3) ≥ 0 := by positivity
  have h52 : (y + z) ≥ (Real.sqrt 51 / 3) := by
    have h15 : (y + z) ^ 2 ≥ (Real.sqrt 51 / 3) ^ 2 := h50
    have h16 : (Real.sqrt 51 / 3) ≥ 0 := h54
    have h17 : (y + z) - (Real.sqrt 51 / 3) ≥ 0 := by
      nlinarith [sq_nonneg ((y + z) - (Real.sqrt 51 / 3)), 
        sq_nonneg ((y + z) + (Real.sqrt 51 / 3)), 
        Real.sqrt_pos.mpr (show (0 : ℝ) < 51 by linarith : (51 : ℝ) > 0)
        ]
    linarith
  linarith