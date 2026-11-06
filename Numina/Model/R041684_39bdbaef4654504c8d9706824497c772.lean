import Mathlib

theorem inequalities_239347 (p q r : ℝ) (hpos : p > 0 ∧ q > 0 ∧ r > 0)
    (n : ℕ) (hpqr : p * q * r = 1) :
    1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) +
    1 / (r ^ n + p ^ n + 1) ≤ 1 := by
  obtain ⟨hp, hq, hr⟩ := hpos
  have h1 : p ^ n > 0 := by positivity
  have h2 : q ^ n > 0 := by positivity
  have h3 : r ^ n > 0 := by positivity
  have h4 : p ^ n * q ^ n * r ^ n = 1 := by
    calc
      p ^ n * q ^ n * r ^ n = (p * q * r) ^ n := by ring
      _ = (1) ^ n := by rw [hpqr]
      _ = 1 := by norm_num
  have h5 : 0 < p ^ n + q ^ n + 1 := by positivity
  have h6 : 0 < q ^ n + r ^ n + 1 := by positivity
  have h7 : 0 < r ^ n + p ^ n + 1 := by positivity
  have h7 : 1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1 ≤ 0 := by
    have h6a : 0 < (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) := by positivity
    have h8 : (1 / (p ^ n + q ^ n + 1) + 1 / (q ^ n + r ^ n + 1) + 1 / (r ^ n + p ^ n + 1) - 1) =
        ( (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (r ^ n + p ^ n + 1) + (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) - (p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1) ) / ((p ^ n + q ^ n + 1) * (q ^ n + r ^ n + 1) * (r ^ n + p ^ n + 1)) := by 
      field_simp
      ring
    rw [h8]
    apply div_nonpos_of_nonpos_of_nonneg
    · -- Show that the numerator is ≤ 0
      nlinarith [sq_nonneg (p ^ n - q ^ n), sq_nonneg (q ^ n - r ^ n), sq_nonneg (r ^ n - p ^ n), 
        sq_nonneg (p ^ n * q ^ n - 1), sq_nonneg (q ^ n * r ^ n - 1), sq_nonneg (r ^ n * p ^ n - 1), 
        h4, mul_pos h1 h2, mul_pos h1 h3, mul_pos h2 h3
      ]
    · -- Show that the denominator is ≥ 0
      positivity
  linarith