import Mathlib

open Real

theorem inequalities_40793 (a b c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hord : a ≥ b ∧ b ≥ c) (hsum : a + b + c = 3) :
    a * b^2 + b * c^2 + c * a^2 ≤ 27 / 8 ∧
    (a * b^2 + b * c^2 + c * a^2 = 27 / 8 ↔ a = 3 / 2 ∧ b = 3 / 2 ∧ c = 0) := by
  constructor
  · -- First we'll prove the inequality
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
         sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0),
         hsum, hord.left, hord.right, 
         mul_nonneg (show 0 ≤ a - c by linarith) (show 0 ≤ b - c by linarith), 
         mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ a - c by linarith)]
  · -- Now let's prove the equality cases
    constructor
    · -- Assume to prove bi-direction
      intro heq
      have h1 : (a - 3 / 2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
             sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0),
             hsum, hord.left, hord.right, 
             mul_nonneg (show 0 ≤ a - c by linarith) (show 0 ≤ b - c by linarith), 
             mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ a - c by linarith)]
      have ha1 : a = 3 / 2 := by nlinarith
      have h2 : (b - 3 / 2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
             sq_nonneg (a - 3 / 2), sq_nonneg (b - 3 / 2), sq_nonneg (c - 0),
             hsum, hord.left, hord.right, 
             mul_nonneg (show 0 ≤ a - c by linarith) (show 0 ≤ b - c by linarith), 
             mul_nonneg (show 0 ≤ a - b by linarith) (show 0 ≤ a - c by linarith)]
      have hb1 : b = 3 / 2 := by nlinarith
      have h3 : c = (0 : ℝ) := by
        nlinarith
      constructor 
      · exact ha1
      constructor
      · exact hb1
      · exact h3
    · -- Assume to prove bi-direction
      rintro ⟨ha1, hb1, hc1⟩
      rw [ha1, hb1, hc1]
      all_goals norm_num