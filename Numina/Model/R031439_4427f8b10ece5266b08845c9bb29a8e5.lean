import Mathlib

open Real

theorem inequalities_224529 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4) ↔
    a + b > c ∧ b + c > a ∧ c + a > b := by
  constructor
  · -- Assume (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4), prove a + b > c ∧ b + c > a ∧ c + a > b
    intro h
    have h1 : (a + b > c) := by
      by_contra h1
      push_neg at h1
      have h2 : c ≥ a + b := by linarith
      nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - c), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (c - (a + b)), 
          mul_nonneg (show 0 ≤ c - (a + b) by linarith) (show 0 ≤ c by linarith)]
    have h2 : (b + c > a) := by
      by_contra h2
      push_neg at h2
      have h3 : a ≥ b + c := by linarith
      nlinarith [sq_nonneg (b - c), sq_nonneg (b + c - a), sq_nonneg (b - a), sq_nonneg (c - a), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (a - (b + c)), 
          mul_nonneg (show 0 ≤ a - (b + c) by linarith) (show 0 ≤ a by linarith)]
    have h3 : (c + a > b) := by
      by_contra h3
      push_neg at h3
      have h4 : b ≥ c + a := by linarith
      nlinarith [sq_nonneg (c - a), sq_nonneg (c + a - b), sq_nonneg (c - b), sq_nonneg (a - b), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          sq_nonneg (b - (c + a)), 
          mul_nonneg (show 0 ≤ b - (c + a) by linarith) (show 0 ≤ b by linarith)]
    constructor
    · exact h1
    constructor
    · exact h2
    · exact h3
  · -- Assume a + b > c ∧ b + c > a ∧ c + a > b, prove (a^2 + b^2 + c^2)^2 > 2 * (a^4 + b^4 + c^4)
    rintro ⟨h1, h2, h3⟩
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith), 
          mul_pos (show 0 < a + b - c by linarith) (show 0 < c + a - b by linarith), 
          mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith),
          sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]