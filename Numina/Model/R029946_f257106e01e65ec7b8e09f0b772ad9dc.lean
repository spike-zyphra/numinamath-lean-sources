import Mathlib

theorem inequalities_231445 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≥ Real.sqrt ((a + b + c) * (a * b + b * c + c * a)) := by
  have h1 : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≥ 0 := by positivity
  have h2 : (a + b + c) * (a * b + b * c + c * a) ≥ 0 := by positivity
  have h3 : Real.sqrt ((a + b + c) * (a * b + b * c + c * a)) ≥ 0 := by positivity
  have h4 : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 ≥ (a + b + c) * (a * b + b * c + c * a) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
              habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h5 : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≥ Real.sqrt ((a + b + c) * (a * b + b * c + c * a)) := by
    have h7 : (Real.sqrt ((a + b + c) * (a * b + b * c + c * a))) ^ 2 = (a + b + c) * (a * b + b * c + c * a) := by
      rw [Real.sq_sqrt]
      all_goals nlinarith [h2]
    have h8 : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≥ 0 := by positivity
    have h9 : (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ^ 2 ≥ (Real.sqrt ((a + b + c) * (a * b + b * c + c * a)) ) ^ 2 := by
      nlinarith [h4, h7]
    have h10 : (Real.sqrt ((a + b + c) * (a * b + b * c + c * a)) ) ≥ 0 := by positivity
    nlinarith [h9, h8, h10]
  exact h5