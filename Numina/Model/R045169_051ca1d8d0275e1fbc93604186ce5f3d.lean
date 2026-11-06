import Mathlib

open Real

theorem inequalities_598312 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4)) :
    a + b > c ∧ a + c > b ∧ b + c > a := by

    constructor
    · -- Prove that $a + b > c$
      by_contra h1
      push_neg at h1
      have h1' : c ≥ a + b := by linarith
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_nonneg (show 0 ≤ c - (a + b) by linarith) (show 0 ≤ a * b by positivity), sq_nonneg (a - b), sq_nonneg (c - (a + b)), sq_nonneg (a * b), sq_nonneg (c^2 - (a + b)^2)]
    · -- Prove that $a + c > b$ and $b + c > a$
      constructor
      · -- Prove that $a + c > b$
        by_contra h2
        push_neg at h2
        have h2' : b ≥ a + c := by linarith
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_nonneg (show 0 ≤ b - (a + c) by linarith) (show 0 ≤ a * c by positivity), sq_nonneg (a - c), sq_nonneg (b - (a + c)), sq_nonneg (a * c), sq_nonneg (b^2 - (a + c)^2)]
      · -- Prove that $b + c > a$
        by_contra h3
        push_neg at h3
        have h3' : a ≥ b + c := by linarith
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_nonneg (show 0 ≤ a - (b + c) by linarith) (show 0 ≤ b * c by positivity), sq_nonneg (b - c), sq_nonneg (a - (b + c)), sq_nonneg (b * c), sq_nonneg (a^2 - (b + c)^2)]