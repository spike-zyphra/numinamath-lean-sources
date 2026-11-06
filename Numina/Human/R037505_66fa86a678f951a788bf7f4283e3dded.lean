import Mathlib
/-a, b, c >0, Proof: 2 * (a + b + c)^3 ≥ 3 * (a^2 + b^2 + c^2 + a * b + b * c + c * a) *
      Real.sqrt (3 * (a * b + b * c + c * a)) -/
theorem inequalities_1674 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    2 * (a + b + c)^3 ≥ 3 * (a^2 + b^2 + c^2 + a * b + b * c + c * a) *
      Real.sqrt (3 * (a * b + b * c + c * a)) := by
  have h2 : Real.sqrt (3 * (a * b + b * c + c * a)) ≤ a + b + c := by
    have h3 : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
    have h4 : Real.sqrt (3 * (a * b + b * c + c * a)) ≤ Real.sqrt ((a + b + c) ^ 2) := Real.sqrt_le_sqrt h3
    rw [Real.sqrt_sq (by nlinarith)] at h4
    linarith
  -- 配方法
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
    Real.sq_sqrt (show 0 ≤ 3 * (a * b + b * c + c * a) by nlinarith),
    mul_self_nonneg (a + b + c - Real.sqrt (3 * (a * b + b * c + c * a))), 
    h2]