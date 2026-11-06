import Mathlib

theorem inequalities_143050 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 ≤ (a + b) * (1 / a + 1 / b) ∧ 9 ≤ (a + b + c) * (1 / a + 1 / b + 1 / c) := by 
  constructor
  · -- To prove that (a + b) * (1 / a + 1 / b) ≥ 4 for any two positive numbers a and b.
    have h1 : (a + b) * (1 / a + 1 / b) - (4 : ℝ) ≥ 0 := by
      have pos1 : a > 0 := by linarith
      have pos2 : b > 0 := by linarith
      have pos3 : a * b > 0 := by nlinarith
      have h2 : (a + b) * (1 / a + 1 / b) - (4 : ℝ) = (a - b) ^ 2 / (a * b) := by
        field_simp
        ring
      rw [h2]
      apply div_nonneg
      · -- Show $(a - b)^2 ≥ 0$
        apply pow_two_nonneg
      · -- Show $a * b > 0$
        positivity
    linarith
  · -- To prove that (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 9 for any three positive numbers a, b, and c.
    have h2 : (a + b + c) * (1 / a + 1 / b + 1 / c) - (9 : ℝ) ≥ 0 := by
      have pos1 : a > 0 := by linarith
      have pos2 : b > 0 := by linarith
      have pos3 : c > 0 := by linarith
      have pos4 : a * b > 0 := by nlinarith
      have pos5 : a * c > 0 := by nlinarith
      have pos6 : b * c > 0 := by nlinarith
      have h3 : (a + b + c) * (1 / a + 1 / b + 1 / c) - (9 : ℝ) = ( (a - b) ^ 2 ) / (a * b) + ( (a - c) ^ 2 ) / (a * c) + ( (b - c) ^ 2 ) / (b * c) := by
        field_simp
        ring
      rw [h3]
      have h4 : (a - b) ^ 2 / (a * b) ≥ 0 := by positivity
      have h5 : (a - c) ^ 2 / (a * c) ≥ 0 := by positivity
      have h6 : (b - c) ^ 2 / (b * c) ≥ 0 := by positivity
      linarith [h4, h5, h6]
    linarith