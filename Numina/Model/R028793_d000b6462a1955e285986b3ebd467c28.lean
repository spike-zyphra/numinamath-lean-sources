import Mathlib

theorem inequalities_56206 (m n p q t : ℝ) (hm : 0 < m) (hn : 0 < n) (hp : 0 < p) (hq : 0 < q) (ht : t = (m + n + p + q) / 2) :
    4 / 5 ≤ m / (t + n + p + q) + n / (t + m + p + q) + p / (t + m + n + q) + q / (t + m + n + p) := by
  have ht1 : t + n + p + q = (m + 3 * n + 3 * p + 3 * q) / 2 := by
    rw [ht]
    linarith
  have ht2 : t + m + p + q = (3 * m + n + 3 * p + 3 * q) / 2 := by
    rw [ht]
    linarith
  have ht3 : t + m + n + q = (3 * m + 3 * n + p + 3 * q) / 2 := by
    rw [ht]
    linarith
  have ht4 : t + m + n + p = (3 * m + 3 * n + 3 * p + q) / 2 := by
    rw [ht]
    linarith
  have h1 : m / (t + n + p + q) = 2 * m / (m + 3 * n + 3 * p + 3 * q) := by
    rw [ht1]
    field_simp
    <;> linarith
  have h2 : n / (t + m + p + q) = 2 * n / (3 * m + n + 3 * p + 3 * q) := by
    rw [ht2]
    field_simp
    <;> linarith
  have h3 : p / (t + m + n + q) = 2 * p / (3 * m + 3 * n + p + 3 * q) := by
    rw [ht3]
    field_simp
    <;> linarith
  have h4 : q / (t + m + n + p) = 2 * q / (3 * m + 3 * n + 3 * p + q) := by
    rw [ht4]
    field_simp
    <;> linarith
  rw [h1, h2, h3, h4]
  have h5 : 0 < m * n * p * q := by
    apply mul_pos
    apply mul_pos
    apply mul_pos
    all_goals linarith
  have h6 : 2 * m / (m + 3 * n + 3 * p + 3 * q) + 2 * n / (3 * m + n + 3 * p + 3 * q) + 2 * p / (3 * m + 3 * n + p + 3 * q) + 2 * q / (3 * m + 3 * n + 3 * p + q) ≥ 4 / 5 := by
    have h7 : 0 < m + 3 * n + 3 * p + 3 * q := by
      linarith
    have h8 : 0 < 3 * m + n + 3 * p + 3 * q := by
      linarith
    have h9 : 0 < 3 * m + 3 * n + p + 3 * q := by
      linarith
    have h10 : 0 < 3 * m + 3 * n + 3 * p + q := by
      linarith
    have h11 : 2 * m / (m + 3 * n + 3 * p + 3 * q) + 2 * n / (3 * m + n + 3 * p + 3 * q) + 2 * p / (3 * m + 3 * n + p + 3 * q) + 2 * q / (3 * m + 3 * n + 3 * p + q) - 4 / 5 ≥ 0 := by
      have h12 : 2 * m / (m + 3 * n + 3 * p + 3 * q) + 2 * n / (3 * m + n + 3 * p + 3 * q) + 2 * p / (3 * m + 3 * n + p + 3 * q) + 2 * q / (3 * m + 3 * n + 3 * p + q) - 4 / 5 =
          ( (2 * m * (3 * m + n + 3 * p + 3 * q) * (3 * m + 3 * n + p + 3 * q) * (3 * m + 3 * n + 3 * p + q) ) +
            (2 * n * (m + 3 * n + 3 * p + 3 * q) * (3 * m + 3 * n + p + 3 * q) * (3 * m + 3 * n + 3 * p + q) ) +
            (2 * p * (m + 3 * n + 3 * p + 3 * q) * (3 * m + n + 3 * p + 3 * q) * (3 * m + 3 * n + 3 * p + q) ) +
            (2 * q * (m + 3 * n + 3 * p + 3 * q) * (3 * m + n + 3 * p + 3 * q) * (3 * m + 3 * n + p + 3 * q) ) -
            (4 / 5 * (m + 3 * n + 3 * p + 3 * q) * (3 * m + n + 3 * p + 3 * q) * (3 * m + 3 * n + p + 3 * q) * (3 * m + 3 * n + 3 * p + q) ) )
          / ( (m + 3 * n + 3 * p + 3 * q) * (3 * m + n + 3 * p + 3 * q) * (3 * m + 3 * n + p + 3 * q) * (3 * m + 3 * n + 3 * p + q) ) := by
        field_simp
        ring
      rw [h12]
      apply div_nonneg
      nlinarith [ 
        sq_nonneg (m - n), sq_nonneg (m - p), sq_nonneg (m - q), 
        sq_nonneg (n - p), sq_nonneg (n - q), sq_nonneg (p - q), 
        sq_nonneg (m * n - p * q), sq_nonneg (m * p - n * q), sq_nonneg (m * q - n * p), 
        mul_pos hm hn, mul_pos hm hp, mul_pos hm hq, 
        mul_pos hn hp, mul_pos hn hq, mul_pos hp hq
      ]
      all_goals positivity
    linarith
  linarith