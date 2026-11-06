import Mathlib


lemma lemma_1 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + (a + b + c)^2 ≤ 4) :
    a + b + c ≤ Real.sqrt 3 := by
  have h1 : (a + b + c) ^ 2 ≤ 3 * (a^2 + b^2 + c^2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have h2 : (a + b + c) ^ 2 ≤ 3 := by
    nlinarith [h, h1]
  have h3 : a + b + c ≤ Real.sqrt 3 := by
    have h4 : (a + b + c) ^ 2 ≤ (3 : ℝ) := h2
    have h5 : 0 ≤ (Real.sqrt 3 : ℝ) := by positivity
    have h6 : (Real.sqrt 3 : ℝ) ^ 2 = (3 : ℝ) := Real.sq_sqrt (by norm_num)
    nlinarith [h4, h6, Real.sqrt_nonneg 3]
  exact h3


theorem inequalities_604332{a b c: ℝ}(apos: 0 < a)(bpos: 0 < b)
  (cpos: 0 < c)(hineq: a^2+b^2+c^2+(a+b+c)^2 ≤ 4):
  (a*b+1)/(a+b)^2 + (b*c+1)/(b+c)^2 + (c*a+1)/(c+a)^2 ≥ 3 := by
  have h1 : a + b + c ≤ Real.sqrt 3 := lemma_1 a b c apos bpos cpos hineq
  have h2 : 0 < a * b := mul_pos apos bpos
  have h3 : 0 < b * c := mul_pos bpos cpos
  have h4 : 0 < c * a := mul_pos cpos apos
  have h5 : 0 < (a + b) ^ 2 := by positivity
  have h6 : 0 < (b + c) ^ 2 := by positivity
  have h7 : 0 < (c + a) ^ 2 := by positivity
  have h3' : (a * b + 1) / (a + b) ^ 2 + (b * c + 1) / (b + c) ^ 2 + (c * a + 1) / (c + a) ^ 2 - 3 ≥ 0 := by
    have H : 0 < (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2 := by positivity
    have h' : (a * b + 1) / (a + b) ^ 2 + (b * c + 1) / (b + c) ^ 2 + (c * a + 1) / (c + a) ^ 2 - 3 =
          ((a * b + 1) * (b + c) ^ 2 * (c + a) ^ 2 + (b * c + 1) * (a + b) ^ 2 * (c + a) ^ 2 + (c * a + 1) * (a + b) ^ 2 * (b + c) ^ 2 - 3 * (a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2) / ((a + b) ^ 2 * (b + c) ^ 2 * (c + a) ^ 2) := by
      field_simp
      ring
    rw [h']
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)), 
          sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          mul_pos apos bpos, mul_pos bpos cpos, mul_pos cpos apos,
          mul_pos (show 0 < a * b from by positivity) (show 0 < b * c from by positivity),
          mul_pos (show 0 < b * c from by positivity) (show 0 < c * a from by positivity),
          mul_pos (show 0 < c * a from by positivity) (show 0 < a * b from by positivity)]
    positivity
  linarith