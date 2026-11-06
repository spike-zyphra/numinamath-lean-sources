import Mathlib

open Real

theorem inequalities_603966 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (2 * sqrt (b ^ 2 - b * c + c ^ 2) + 3 * a) +
    b / (2 * sqrt (c ^ 2 - c * a + a ^ 2) + 3 * b) +
    c / (2 * sqrt (a ^ 2 - a * b + b ^ 2) + 3 * c) ≤ 3 / 5 := by 
  have h1 : 2 * sqrt (b ^ 2 - b * c + c ^ 2) ≥ b + c := by
    have h2 : b ^ 2 - b * c + c ^ 2 ≥ ( (b + c) / 2 ) ^ 2 := by
      nlinarith [sq_nonneg (b - c)]
    have h3 : sqrt (b ^ 2 - b * c + c ^ 2) ≥ sqrt ( ( (b + c) / 2 ) ^ 2 ) := Real.sqrt_le_sqrt (h2)
    have h4 : sqrt ( ( (b + c) / 2 ) ^ 2 ) = (b + c) / 2 := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h3, h4]
  have h1' : a / (2 * sqrt (b ^ 2 - b * c + c ^ 2) + 3 * a) ≤ a / (b + c + 3 * a) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h1]
  have h2 : 2 * sqrt (c ^ 2 - c * a + a ^ 2) ≥ c + a := by
    have h2 : c ^ 2 - c * a + a ^ 2 ≥ ( (c + a) / 2 ) ^ 2 := by
      nlinarith [sq_nonneg (c - a)]
    have h3 : sqrt (c ^ 2 - c * a + a ^ 2) ≥ sqrt ( ( (c + a) / 2 ) ^ 2 ) := Real.sqrt_le_sqrt (h2)
    have h4 : sqrt ( ( (c + a) / 2 ) ^ 2 ) = (c + a) / 2 := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h3, h4]
  have h2' : b / (2 * sqrt (c ^ 2 - c * a + a ^ 2) + 3 * b) ≤ b / (c + a + 3 * b) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h2]
  have h3 : 2 * sqrt (a ^ 2 - a * b + b ^ 2) ≥ a + b := by
    have h2 : a ^ 2 - a * b + b ^ 2 ≥ ( (a + b) / 2 ) ^ 2 := by
      nlinarith [sq_nonneg (a - b)]
    have h3 : sqrt (a ^ 2 - a * b + b ^ 2) ≥ sqrt ( ( (a + b) / 2 ) ^ 2 ) := Real.sqrt_le_sqrt (h2)
    have h4 : sqrt ( ( (a + b) / 2 ) ^ 2 ) = (a + b) / 2 := by
      rw [Real.sqrt_sq (by linarith)]
    nlinarith [h3, h4]
  have h3' : c / (2 * sqrt (a ^ 2 - a * b + b ^ 2) + 3 * c) ≤ c / (a + b + 3 * c) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h3]
  have h4 : a / (b + c + 3 * a) + b / (c + a + 3 * b) + c / (a + b + 3 * c) ≤ 3 / 5 := by
    have h1 : a / (b + c + 3 * a) + b / (c + a + 3 * b) + c / (a + b + 3 * c) - 3 / 5 ≤ 0 := by
      have h3 : a / (b + c + 3 * a) + b / (c + a + 3 * b) + c / (a + b + 3 * c) - 3 / 5 =
          (5 * a * (c + a + 3 * b) * (a + b + 3 * c) + 5 * b * (b + c + 3 * a) * (a + b + 3 * c) + 5 * c * (b + c + 3 * a) * (c + a + 3 * b) - 3 * (b + c + 3 * a) * (c + a + 3 * b) * (a + b + 3 * c)) / (5 * (b + c + 3 * a) * (c + a + 3 * b) * (a + b + 3 * c)) := by 
          field_simp
          ring
      rw [h3] at *
      apply div_nonpos_of_nonpos_of_nonneg
      · -- Nominator less than or equal to 0
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
          sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), 
          sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
      · -- Denominator greater than or equal to 0
        positivity
    linarith
  linarith [h1', h2', h3', h4]