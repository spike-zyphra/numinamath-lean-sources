import Mathlib

open Real

theorem inequalities_267830 (a b c d m n : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hm : 0 < m) (hn : 0 < n) :
    sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) ≥ sqrt (a * b) + sqrt (c * d) := by

  have h1 : 0 < m * a + n * c := by
    positivity

  have h2 : 0 < (b / m) + (d / n) := by
    have hb1 : 0 < b / m := by
      apply div_pos
      all_goals linarith
    have hd1 : 0 < d / n := by
      apply div_pos
      all_goals linarith
    linarith

  have h3 : sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) = sqrt ((m * a + n * c) * ((b / m) + (d / n)) ) := by
    rw [← Real.sqrt_mul (by positivity)]

  rw [h3] at *

  have h4 : Real.sqrt ((m * a + n * c) * ((b / m) + (d / n)) ) ≥ 0 := by positivity
  have h5 : sqrt (a * b) + sqrt (c * d) ≥ 0 := by positivity

  have h6 : (Real.sqrt ((m * a + n * c) * ((b / m) + (d / n)))) ^ 2 ≥ (sqrt (a * b) + sqrt (c * d)) ^ 2 := by
    have h7 : (Real.sqrt ((m * a + n * c) * ((b / m) + (d / n)) ) ) ^ 2 = (m * a + n * c) * ((b / m) + (d / n)) := by
      rw [Real.sq_sqrt]
      positivity
    have h8 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = (sqrt (a * b)) ^ 2 + (sqrt (c * d)) ^ 2 + 2 * (sqrt (a * b) * sqrt (c * d)) := by
      ring
    have h9 : (sqrt (a * b)) ^ 2 = a * b := by
      rw [Real.sq_sqrt]
      positivity
    have h10 : (sqrt (c * d)) ^ 2 = c * d := by
      rw [Real.sq_sqrt]
      positivity
    have h11 : sqrt (a * b) * sqrt (c * d) = Real.sqrt (a * b * c * d) := by
      have h11 : sqrt (a * b) * sqrt (c * d) = Real.sqrt ((a * b) * (c * d)) := by
        rw [← Real.sqrt_mul (by positivity)]
      have h12 : (a * b) * (c * d) = a * b * c * d := by
        ring
      rw [h12] at h11
      linarith [h11]
    have h12 : (m * a + n * c) * ((b / m) + (d / n)) ≥ a * b + c * d + 2 * Real.sqrt (a * b * c * d) := by
      have h13 : (m * a + n * c) * ((b / m) + (d / n)) = a * b + c * d + (m * a * d / n) + (n * c * b / m) := by
        field_simp
        ring
      have h14 : m * a * d / n + n * c * b / m ≥ 2 * Real.sqrt (a * b * c * d) := by 
        have h15 : (m * a * d / n + n * c * b / m) - 2 * Real.sqrt (a * b * c * d) ≥ 0 := by 
          have h16 : m * a * d / n + n * c * b / m - 2 * Real.sqrt (a * b * c * d) = 
            (Real.sqrt (m * a * d / n) - Real.sqrt (n * c * b / m)) ^ 2 + 2 * (Real.sqrt (m * a * d / n) * Real.sqrt (n * c * b / m) - Real.sqrt (a * b * c * d)) := by 
            nlinarith [Real.sq_sqrt (show 0 ≤ m * a * d / n by positivity), Real.sq_sqrt (show 0 ≤ n * c * b / m by positivity)]
          have h17 : Real.sqrt (m * a * d / n) * Real.sqrt (n * c * b / m) = Real.sqrt (a * b * c * d) := by
            have h18 : Real.sqrt (m * a * d / n) * Real.sqrt (n * c * b / m) = Real.sqrt ((m * a * d / n) * (n * c * b / m)) := by
              rw [← Real.sqrt_mul (by positivity)]
            have h19 : (m * a * d / n) * (n * c * b / m) = a * b * c * d := by
              field_simp
              ring
            rw [h19] at h18
            linarith [h18]
          rw [h17] at h16
          have h18 : (Real.sqrt (m * a * d / n) - Real.sqrt (n * c * b / m)) ^ 2 ≥ 0 := by 
            apply sq_nonneg
          nlinarith [Real.sqrt_nonneg (a * b * c * d), Real.sqrt_nonneg (m * a * d / n), Real.sqrt_nonneg (n * c * b / m)  ]
        linarith
      linarith [h13, h14]
    nlinarith [h7, h8, h9, h10, h11, h12, Real.sqrt_nonneg (a * b * c * d), Real.sq_sqrt (show a * b * c * d ≥ 0 by positivity), Real.sqrt_nonneg ((m * a + n * c) * ((b / m) + (d / n)) ), Real.sq_sqrt (show (m * a + n * c) * ((b / m) + (d / n)) ≥ 0 by positivity) ]
  nlinarith [Real.sqrt_nonneg ((m * a + n * c) * ((b / m) + (d / n)) ), Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), h6, h4, h5]