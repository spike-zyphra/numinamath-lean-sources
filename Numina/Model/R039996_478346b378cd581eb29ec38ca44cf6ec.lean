import Mathlib

theorem inequalities_215529 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    |(a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a)| < 1 := by
  have h1 : 0 < a + b := by linarith
  have h2 : 0 < b + c := by linarith
  have h3 : 0 < c + a := by linarith
  have h4 : -1 < (a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a) := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have h5' : (a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a) + 1 > 0 := by 
      have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
      have h5'' : (a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a) + 1 =
        ((a - b) * (b + c) * (c + a) + (b - c) * (a + b) * (c + a) + (c - a) * (a + b) * (b + c) + (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a)) := by
        field_simp
        ring
      rw [h5'']
      apply div_pos
      -- Prove numerator is positive
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      all_goals positivity
    linarith
  have h5 : (a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a) < 1 := by
    have pos1 : 0 < (a + b) * (b + c) * (c + a) := by positivity
    have h1 : (a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a) - 1 < 0 := by 
      have h1' : (a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a) - 1 =
        ((a - b) * (b + c) * (c + a) + (b - c) * (a + b) * (c + a) + (c - a) * (a + b) * (b + c) - (a + b) * (b + c) * (c + a)) / ((a + b) * (b + c) * (c + a)) := by
        field_simp
        ring
      rw [h1']
      apply div_neg_of_neg_of_pos
      -- Prove numerator is negative
      nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      all_goals positivity
    linarith
  have h7 : |(a - b) / (a + b) + (b - c) / (b + c) + (c - a) / (c + a)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact h7