import Mathlib

open Real

theorem inequalities_163899 {a b c d : ℝ} (ha : 0 < d) (hd : d < c) (hc : c < b) (hb : b < a)
    (X Y Z : ℝ) (hX : X = sqrt (a * b) + sqrt (c * d)) (hY : Y = sqrt (a * c) + sqrt (b * d))
    (hZ : Z = sqrt (a * d) + sqrt (b * c)) : Z < Y ∧ Y < X := by
  have h1 : Z < Y := by
    rw [hZ, hY]
    have h2 : 0 < a := by linarith
    have h3 : 0 < b := by linarith
    have h4 : 0 < c := by linarith
    have h5 : 0 < d := by linarith
    have h6 : sqrt (a * d) + sqrt (b * c) ≥ 0 := by positivity
    have h7 : sqrt (a * c) + sqrt (b * d) ≥ 0 := by positivity
    suffices (sqrt (a * d) + sqrt (b * c)) ^ 2 < (sqrt (a * c) + sqrt (b * d)) ^ 2 by nlinarith
    have h8 : (sqrt (a * d) + sqrt (b * c)) ^ 2 = (a * d) + (b * c) + 2 * (sqrt (a * d) * sqrt (b * c)) := by
      nlinarith [Real.sqrt_nonneg (a * d), Real.sqrt_nonneg (b * c), Real.sq_sqrt (show 0 ≤ a * d by positivity), Real.sq_sqrt (show 0 ≤ b * c by positivity)]
    have h9 : (sqrt (a * c) + sqrt (b * d)) ^ 2 = (a * c) + (b * d) + 2 * (sqrt (a * c) * sqrt (b * d)) := by
      nlinarith [Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sq_sqrt (show 0 ≤ a * c by positivity), Real.sq_sqrt (show 0 ≤ b * d by positivity)]
    have h10 : sqrt (a * d) * sqrt (b * c) = sqrt (a * b * c * d) := by
      have h11 : sqrt (a * d) * sqrt (b * c) = sqrt ((a * d) * (b * c)) := by
        rw [← Real.sqrt_mul (by positivity)]
      have h12 : (a * d) * (b * c) = a * b * c * d := by
        ring
      rw [h12] at h11
      exact h11
    have h13 : sqrt (a * c) * sqrt (b * d) = sqrt (a * b * c * d) := by
      have h14 : sqrt (a * c) * sqrt (b * d) = sqrt ((a * c) * (b * d)) := by
        rw [← Real.sqrt_mul (by positivity)]
      have h15 : (a * c) * (b * d) = a * b * c * d := by
        ring
      rw [h15] at h14
      exact h14
    rw [h8, h9, h10, h13]
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), mul_pos (show 0 < a - b by linarith) (show 0 < c - d by linarith), mul_pos (show 0 < a - c by linarith) (show 0 < b - d by linarith), mul_pos (show 0 < a - d by linarith) (show 0 < b - c by linarith)]
  have h2 : Y < X := by
    rw [hY, hX]
    have h14 : 0 < a := by linarith
    have h15 : 0 < b := by linarith
    have h16 : 0 < c := by linarith
    have h17 : 0 < d := by linarith
    have h18 : sqrt (a * c) + sqrt (b * d) ≥ 0 := by positivity
    have h19 : sqrt (a * b) + sqrt (c * d) ≥ 0 := by positivity
    suffices (sqrt (a * c) + sqrt (b * d)) ^ 2 < (sqrt (a * b) + sqrt (c * d)) ^ 2 by nlinarith
    have h20 : (sqrt (a * c) + sqrt (b * d)) ^ 2 = (a * c) + (b * d) + 2 * (sqrt (a * c) * sqrt (b * d)) := by
      nlinarith [Real.sqrt_nonneg (a * c), Real.sqrt_nonneg (b * d), Real.sq_sqrt (show 0 ≤ a * c by positivity), Real.sq_sqrt (show 0 ≤ b * d by positivity)]
    have h21 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = (a * b) + (c * d) + 2 * (sqrt (a * b) * sqrt (c * d)) := by
      nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sq_sqrt (show 0 ≤ a * b by positivity), Real.sq_sqrt (show 0 ≤ c * d by positivity)]
    have h22 : sqrt (a * c) * sqrt (b * d) = sqrt (a * b * c * d) := by
      have h23 : sqrt (a * c) * sqrt (b * d) = sqrt ((a * c) * (b * d)) := by
        rw [← Real.sqrt_mul (by positivity)]
      have h24 : (a * c) * (b * d) = a * b * c * d := by
        ring
      rw [h24] at h23
      exact h23
    have h25 : sqrt (a * b) * sqrt (c * d) = sqrt (a * b * c * d) := by
      have h26 : sqrt (a * b) * sqrt (c * d) = sqrt ((a * b) * (c * d)) := by
        rw [← Real.sqrt_mul (by positivity)]
      have h27 : (a * b) * (c * d) = a * b * c * d := by
        ring
      rw [h27] at h26
      exact h26
    rw [h20, h21, h22, h25]
    nlinarith [sq_nonneg (a - b), sq_nonneg (c - d), mul_pos (show 0 < a - b by linarith) (show 0 < b - c by linarith), mul_pos (show 0 < a - c by linarith) (show 0 < b - d by linarith), mul_pos (show 0 < a - d by linarith) (show 0 < b - c by linarith)]
  constructor
  · exact h1
  · exact h2