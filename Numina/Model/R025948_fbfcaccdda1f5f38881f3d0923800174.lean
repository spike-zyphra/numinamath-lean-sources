import Mathlib

open Real

lemma lemma_1 (m n : ℝ) (h₀ : 0 < m) (h₁ : 0 < n) :
    2 * sqrt (m * n) ≤ m + n := by
  have h5 : 0 ≤ (sqrt m - sqrt n) ^ 2 := by positivity
  have h7 : (sqrt m) ^ 2 = m := Real.sq_sqrt (by linarith)
  have h8 : (sqrt n) ^ 2 = n := Real.sq_sqrt (by linarith)
  have h9 : sqrt (m * n) = sqrt m * sqrt n := by
    rw [Real.sqrt_mul (by nlinarith)]
  have h10 : 2 * sqrt (m * n) = 2 * (sqrt m * sqrt n) := by
    rw [h9]
  have h11 : 2 * (sqrt m * sqrt n) ≤ m + n := by
    nlinarith [Real.sqrt_nonneg (m), Real.sqrt_nonneg (n), Real.sq_sqrt (show (0 : ℝ) ≤ m by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ n by linarith), sq_nonneg (sqrt m - sqrt n), sq_nonneg (sqrt m + sqrt n), mul_nonneg (Real.sqrt_nonneg (m)) (Real.sqrt_nonneg (n)), mul_nonneg (show (0 : ℝ) ≤ m by linarith) (show (0 : ℝ) ≤ n by linarith)]
  linarith [h10, h11]

theorem inequalities_174105 (a b c d m n : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hm : 0 < m) (hn : 0 < n) :
    sqrt (a * b) + sqrt (c * d) ≤ sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) := by
  have h1 : 0 ≤ m * a + n * c := by positivity
  have h2 : 0 ≤ (b / m) + (d / n) := by positivity
  have h3 : 0 ≤ m * a := by positivity
  have h4 : 0 ≤ n * c := by positivity
  have h5 : 0 ≤ (b / m) := by positivity
  have h6 : 0 ≤ (d / n) := by positivity
  have h7 : sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) = sqrt ((m * a + n * c) * ((b / m) + (d / n))) := by
    rw [← Real.sqrt_mul (by positivity)]
  have h8 : (sqrt (a * b) + sqrt (c * d)) ^ 2 ≤ (m * a + n * c) * ((b / m) + (d / n)) := by
    have h9 : (sqrt (a * b) + sqrt (c * d)) ^ 2 = (sqrt (a * b)) ^ 2 + (sqrt (c * d)) ^ 2 + 2 * (sqrt (a * b) * sqrt (c * d)) := by
      ring
    have h10 : (sqrt (a * b)) ^ 2 = a * b := by
      rw [Real.sq_sqrt]
      nlinarith
    have h11 : (sqrt (c * d)) ^ 2 = c * d := by
      rw [Real.sq_sqrt]
      nlinarith
    have h12 : 2 * (sqrt (a * b) * sqrt (c * d)) = 2 * (sqrt (a * b * (c * d)) ) := by
      have h13 : sqrt (a * b) * sqrt (c * d) = sqrt ((a * b) * (c * d)) := by
        rw [← Real.sqrt_mul (by positivity)]
      rw [h13]
    have h13 : (m * a + n * c) * ((b / m) + (d / n)) = a * b + c * d + (m * a * d / n) + (n * c * b / m) := by
      field_simp
      ring
    have h14 : 2 * (sqrt (a * b * (c * d)) ) ≤ (m * a * d / n) + (n * c * b / m) := by
      have h17 : 0 < m * a * d / n := by positivity
      have h18 : 0 < n * c * b / m := by positivity
      have h19 : 2 * sqrt (a * b * (c * d)) = 2 * sqrt ((m * a * d / n) * (n * c * b / m)) := by
        have h33 : (m * a * d / n) * (n * c * b / m) = a * b * (c * d) := by
          field_simp
          ring
        rw [h33]
      rw [h19]
      have h22 : 2 * sqrt ((m * a * d / n) * (n * c * b / m)) ≤ (m * a * d / n) + (n * c * b / m) := by
        nlinarith [sq_nonneg (sqrt ((m * a * d / n) * (n * c * b / m)) - (m * a * d / n)), sq_nonneg (sqrt ((m * a * d / n) * (n * c * b / m)) - (n * c * b / m)), Real.sqrt_nonneg ((m * a * d / n) * (n * c * b / m)), Real.sqrt_nonneg (m * a * d / n), Real.sqrt_nonneg (n * c * b / m),
          sq_nonneg (sqrt (m * a * d / n) - sqrt (n * c * b / m)), Real.mul_self_sqrt (show 0 ≤ (m * a * d / n) * (n * c * b / m) by positivity), Real.mul_self_sqrt (show 0 ≤ m * a * d / n by positivity), Real.mul_self_sqrt (show 0 ≤ n * c * b / m by positivity),
          mul_nonneg (Real.sqrt_nonneg (m * a * d / n)) (Real.sqrt_nonneg (n * c * b / m)), Real.sqrt_nonneg ((m * a * d / n) * (n * c * b / m)), Real.mul_self_sqrt (show 0 ≤ (m * a * d / n) * (n * c * b / m) by positivity)]
      linarith
    nlinarith [Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (m * a * d / n), Real.sqrt_nonneg (n * c * b / m), h10, h11, h13, h14
    ]
  have h15 : sqrt ( (sqrt (a * b) + sqrt (c * d)) ^ 2 ) ≤ sqrt ( (m * a + n * c) * ((b / m) + (d / n)) ) := Real.sqrt_le_sqrt (h8)
  have h16 : sqrt ( (sqrt (a * b) + sqrt (c * d)) ^ 2 ) = sqrt (a * b) + sqrt (c * d) := by
    rw [Real.sqrt_sq (show 0 ≤ sqrt (a * b) + sqrt (c * d) by positivity)]
  have h17 : sqrt ( (m * a + n * c) * ((b / m) + (d / n)) ) = sqrt (m * a + n * c) * sqrt ((b / m) + (d / n)) := by
    rw [Real.sqrt_mul (by positivity)]
  rw [h16, h17] at h15
  linarith [h15, Real.sqrt_nonneg (a * b), Real.sqrt_nonneg (c * d), Real.sqrt_nonneg (m * a + n * c), Real.sqrt_nonneg ((b / m) + (d / n)), h7
  ]