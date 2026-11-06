import Mathlib

theorem inequalities_600791 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a)) ≥ (a + b + c) / 2 := by
  have ha1 : 0 < a := ha
  have hb1 : 0 < b := hb
  have hc1 : 0 < c := hc
  have ha2 : 0 < a + b := by linarith
  have hb2 : 0 < b + c := by linarith
  have hc2 : 0 < c + a := by linarith
  have h1 : a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) - (a + b + c) / 2 ≥ 0 := by
    have pos1 : 0 < 2 * (a + b) * (b + c) * (c + a) := by positivity
    have h2 : (a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) - (a + b + c) / 2) ≥ 0 := by
      have eq1 : (a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + a) - (a + b + c) / 2) = 
                  (2 * a ^ 2 * (b + c) * (c + a) + 2 * b^2 * (a + b) * (c + a) + 2 * c^2 * (a + b) * (b + c) - 
                   (a + b + c) * (a + b) * (b + c) * (c + a)) / (2 * (a + b) * (b + c) * (c + a)) := by
        field_simp [ha2, hb2, hc2]
        ring
      rw [eq1]
      apply div_nonneg 
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), 
                mul_pos ha1 hb1, mul_pos hb1 hc1, mul_pos ha1 hc1]
      positivity
    linarith
  linarith