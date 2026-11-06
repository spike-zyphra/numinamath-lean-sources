import Mathlib

theorem negated_inequalities_90039 (a b c : ℝ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : (a + b) * (b + c) * (c + a) = 1) :
    a * b + b * c + c * a ≤ 3 / 4 := by
  have h1 : 0 < a * b := by
    nlinarith
  have h2 : a * b ≤ (a + b) ^ 2 / 4 := by 
    nlinarith [sq_nonneg (a - b)]
  have h3 : b * c ≤ (b + c) ^ 2 / 4 := by 
    nlinarith [sq_nonneg (b - c)]
  have h4 : c * a ≤ (c + a) ^ 2 / 4 := by 
    nlinarith [sq_nonneg (c - a)]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]