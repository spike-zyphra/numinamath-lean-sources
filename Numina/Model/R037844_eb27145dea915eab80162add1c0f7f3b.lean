import Mathlib

theorem inequalities_605763 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + b + c = 1) :
  13 ≤ (5 + 2 * b + c^2) / (1 + a) + (5 + 2 * c + a^2) / (1 + b) + (5 + 2 * a + b^2) / (1 + c) := by
  have h1 : 0 < 1 + a := by linarith
  have h2 : 0 < 1 + b := by linarith
  have h3 : 0 < 1 + c := by linarith
  have h9 : (5 + 2 * b + c^2) / (1 + a) + (5 + 2 * c + a^2) / (1 + b) + (5 + 2 * a + b^2) / (1 + c) ≥ 13 := by
    have h10 : 0 < (1 + a) * (1 + b) * (1 + c) := by positivity
    have h11 : (5 + 2 * b + c ^ 2) / (1 + a) + (5 + 2 * c + a ^ 2) / (1 + b) + (5 + 2 * a + b ^ 2) / (1 + c) - 13 ≥ 0 := by
      have eq21 : (5 + 2 * b + c ^ 2) / (1 + a) + (5 + 2 * c + a ^ 2) / (1 + b) + (5 + 2 * a + b ^ 2) / (1 + c) - 13 = 
          ( (5 + 2 * b + c ^ 2) * (1 + b) * (1 + c) + (5 + 2 * c + a ^ 2) * (1 + a) * (1 + c) + (5 + 2 * a + b ^ 2) * (1 + a) * (1 + b) - 13 * ((1 + a) * (1 + b) * (1 + c)) ) / ((1 + a) * (1 + b) * (1 + c)) := by 
        field_simp
        ring
      rw [eq21]
      have h44 : (5 + 2 * b + c^2) * (1 + b) * (1 + c) + (5 + 2 * c + a^2) * (1 + a) * (1 + c) + (5 + 2 * a + b^2) * (1 + a) * (1 + b) - 13 * ((1 + a) * (1 + b) * (1 + c)) ≥ 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                sq_nonneg (a - 1 / 3), sq_nonneg (b - 1 / 3), sq_nonneg (c - 1 / 3),
                mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
      apply div_nonneg 
      exact h44
      positivity 
    linarith 
  linarith [h9]