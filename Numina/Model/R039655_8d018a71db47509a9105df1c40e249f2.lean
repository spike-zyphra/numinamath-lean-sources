import Mathlib

open Real
open scoped BigOperators

theorem inequalities_124177 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 ∧
  (a + b + c) ^ 2 < 4 * (a * b + b * c + c * a) ∧
  (3 * (a * b + b * c + c * a) = (a + b + c) ^ 2 ↔
    (a = b ∧ b = c)) := by
  constructor
  · -- Prove the first inequality: 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      h, h', h'']
  constructor
  · -- Prove the second inequality: (a + b + c)^2 < 4 * (a * b + b * c + c * a)
    nlinarith [sq_pos_of_pos (show 0 < (a + b - c) by linarith),
      sq_pos_of_pos (show 0 < (a + c - b) by linarith),
      sq_pos_of_pos (show 0 < (b + c - a) by linarith)]
  · -- Prove the equality case
    constructor
    · -- Assume 3 * (a * b + b * c + c * a) = (a + b + c) ^ 2, show a = b ∧ b = c
      intro heq
      have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
        nlinarith [heq]
      have h2 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have h3 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      -- From squares equal to zero, the differences are zero.
      have h5 : a - b = 0 := by
        rwa [sq_eq_zero_iff] at h2
      have h6 : b - c = 0 := by
        rwa [sq_eq_zero_iff] at h3
      constructor
      · -- Show a = b
        linarith
      · -- Show b = c
        linarith
    · -- Assume a = b ∧ b = c, show 3 * (a * b + b * c + c * a) = (a + b + c) ^ 2
      rintro ⟨rfl, rfl⟩
      nlinarith