import Mathlib

theorem inequalities_293003 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxi : x ≤ 1) :
    x * y + y + 2 * z ≥ 4 * Real.sqrt (x * y * z) := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    exact hx
    exact hy
    exact hz

  have h2 : Real.sqrt (x * y * z) ≥ 0 := by
    apply Real.sqrt_nonneg

  have h3 : x * y + y + 2 * z ≥ 0 := by
    have h4 : x * y > 0 := mul_pos hx hy
    have h6 : x * y + y + 2 * z > 0 := by
      have h4 : x * y > 0 := mul_pos hx hy
      have h7 : (x * y + y) > 0 := by
        nlinarith
      have h8 : 2 * z > 0 := by
        nlinarith
      nlinarith
    linarith

  have h4 : (4 * Real.sqrt (x * y * z)) ^ 2 = 16 * (x * y * z) := by
    calc
      (4 * Real.sqrt (x * y * z)) ^ 2 = 16 * (Real.sqrt (x * y * z) ^ 2) := by
        ring_nf
      _ = 16 * (x * y * z) := by
        rw [Real.sq_sqrt (by positivity)]

  have h5 : (x * y + y + 2 * z) ^ 2 ≥ 16 * (x * y * z) := by
    nlinarith [sq_nonneg (x * y - y), sq_nonneg (y - z), sq_nonneg (z - (x * y)), 
      sq_nonneg (x - 1), sq_nonneg (y - z), sq_nonneg (x * y - z),
      sq_nonneg (2 * z - (x * y + y)), 
      mul_nonneg (show (0 : ℝ) ≤ 1 - x by linarith) (show (0 : ℝ) ≤ 1 - x by linarith), 
      mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
    ]

  have h7 : (x * y + y + 2 * z) ≥ 4 * Real.sqrt (x * y * z) := by
    have h7 : (4 * Real.sqrt (x * y * z)) ≥ 0 := by
      nlinarith [Real.sqrt_nonneg (x * y * z), show (4 : ℝ) > 0 by norm_num]
    nlinarith [sq_nonneg ( (x * y + y + 2 * z) - 4 * Real.sqrt (x * y * z) ), 
      Real.sqrt_nonneg (x * y * z), h1, Real.sq_sqrt (show 0 ≤ x * y * z by positivity), h2
    ]

  exact h7