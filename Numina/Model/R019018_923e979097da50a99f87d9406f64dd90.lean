import Mathlib
theorem inequalities_597544 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    (a^2 - b * c) / (2 * a^2 + b^2 + c^2) + (b^2 - c * a) / (2 * b^2 + c^2 + a^2) +
    (c^2 - a * b) / (2 * c^2 + a^2 + b^2) ≥ 0 := by 
  have h1 : 0 ≤ 2 * a^2 + b^2 + c^2 := by positivity
  have h2 : 0 ≤ 2 * b^2 + c^2 + a^2 := by positivity
  have h3 : 0 ≤ 2 * c^2 + a^2 + b^2 := by positivity
  by_cases h1' : 2 * a^2 + b^2 + c^2 > 0
  · by_cases h2' : 2 * b^2 + c^2 + a^2 > 0
    · by_cases h3' : 2 * c^2 + a^2 + b^2 > 0
      · have h4 : (a^2 - b * c) / (2 * a^2 + b^2 + c^2) + (b^2 - c * a) / (2 * b^2 + c^2 + a^2) + (c^2 - a * b) / (2 * c^2 + a^2 + b^2) =
          ((a^2 - b * c) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) + (b^2 - c * a) * (2 * a^2 + b^2 + c^2) * (2 * c^2 + a^2 + b^2) + (c^2 - a * b) * (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2)) / ((2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2)) := by
          field_simp
          <;> ring
        rw [h4] at *
        have h5 : (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) > 0 := by positivity
        have h6 : (a^2 - b * c) * (2 * b^2 + c^2 + a^2) * (2 * c^2 + a^2 + b^2) + (b^2 - c * a) * (2 * a^2 + b^2 + c^2) * (2 * c^2 + a^2 + b^2) + (c^2 - a * b) * (2 * a^2 + b^2 + c^2) * (2 * b^2 + c^2 + a^2) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
            sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
            mul_nonneg (show 0 ≤ a^2 by positivity) (show 0 ≤ b^2 by positivity), 
            mul_nonneg (show 0 ≤ a^2 by positivity) (show 0 ≤ c^2 by positivity), 
            mul_nonneg (show 0 ≤ b^2 by positivity) (show 0 ≤ c^2 by positivity)]
        apply div_nonneg
        · linarith
        · positivity
      · -- When the third denominator is 0.
        have h20 : 2 * c^2 + a^2 + b^2 = 0 := by
          nlinarith
        have h21 : a^2 + b^2 + c^2 = 0 := by
          nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
        have ha0 : a = 0 := by
          nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
        have hb0 : b = 0 := by
          nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
        have hc0 : c = 0 := by
          nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
        rw [ha0, hb0, hc0]
        norm_num
    · -- When the second denominator is 0.
      have h13 : 2 * b^2 + c^2 + a^2 = 0 := by
        nlinarith
      have h14 : a^2 + b^2 + c^2 = 0 := by
        nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
      have ha0 : a = 0 := by
        nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
      have hb0 : b = 0 := by
        nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
      have hc0 : c = 0 := by
        nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
      rw [ha0, hb0, hc0]
      norm_num
  · -- When the first denominator is 0.
    have h1' : 2 * a^2 + b^2 + c^2 = 0 := by
      nlinarith
    have h14 : a^2 + b^2 + c^2 = 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
    have ha0 : a = 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
    have hb0 : b = 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
    have hc0 : c = 0 := by
      nlinarith [sq_nonneg (a), sq_nonneg (b), sq_nonneg (c)]
    rw [ha0, hb0, hc0]
    norm_num