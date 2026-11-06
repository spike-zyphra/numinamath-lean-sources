import Mathlib

theorem inequalities_69682 (m n p q : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) (ht : t = (m + n + p + q) / 2) :
    4 / 5 ≤ m / (t + n + p + q) + n / (t + p + q + m) + p / (t + q + m + n) +
    q / (t + m + n + p) := by 
  rw [ht]
  have pos1 : 0 < (m + n + p + q) / 2 + n + p + q := by 
    linarith 
  have pos2 : 0 < (m + n + p + q) / 2 + p + q + m := by 
    linarith 
  have pos3 : 0 < (m + n + p + q) / 2 + q + m + n := by 
    linarith 
  have pos4 : 0 < (m + n + p + q) / 2 + m + n + p := by 
    linarith 
  have h5 : m / ((m + n + p + q) / 2 + n + p + q) + n / ((m + n + p + q) / 2 + p + q + m) + p / ((m + n + p + q) / 2 + q + m + n) + q / ((m + n + p + q) / 2 + m + n + p) - 4 / 5 ≥ 0 := by 
    have pos1 : 0 < (m + n + p + q) / 2 + n + p + q := by 
      linarith 
    have pos2 : 0 < (m + n + p + q) / 2 + p + q + m := by 
      linarith 
    have pos3 : 0 < (m + n + p + q) / 2 + q + m + n := by 
      linarith 
    have pos4 : 0 < (m + n + p + q) / 2 + m + n + p := by 
      linarith 
    have h7 : m / ((m + n + p + q) / 2 + n + p + q) + n / ((m + n + p + q) / 2 + p + q + m) + p / ((m + n + p + q) / 2 + q + m + n) + q / ((m + n + p + q) / 2 + m + n + p) - 4 / 5 =
        (5 * m * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p) +
        5 * n * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p) +
        5 * p * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + m + n + p) +
        5 * q * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) - 4 * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p)) / (5 * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p)) := by 
      field_simp
      <;> ring
    rw [h7] at *
    have pos5 : 0 < 5 * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p) := by
      positivity 
    have h6 : 5 * m * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p) + 5 * n * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p) + 5 * p * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + m + n + p) + 5 * q * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) - 4 * ((m + n + p + q) / 2 + n + p + q) * ((m + n + p + q) / 2 + p + q + m) * ((m + n + p + q) / 2 + q + m + n) * ((m + n + p + q) / 2 + m + n + p) ≥ 0 := by 
      nlinarith [sq_nonneg (m - n), sq_nonneg (m - p), sq_nonneg (m - q), sq_nonneg (n - p), sq_nonneg (n - q), sq_nonneg (p - q), 
          sq_nonneg (m + n - p - q), sq_nonneg (m + p - n - q), sq_nonneg (m + q - n - p), 
          mul_pos hm hn, mul_pos hm hp, mul_pos hm hq, 
          mul_pos hn hp, mul_pos hn hq, mul_pos hp hq 
        ]
    apply div_nonneg 
    linarith 
    all_goals 
      positivity 
  linarith