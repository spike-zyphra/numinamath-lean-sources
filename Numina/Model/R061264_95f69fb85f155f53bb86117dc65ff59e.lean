import Mathlib

open Real

theorem inequalities_257402 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a + b < 2) :
    1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ≤ 2 / (1 + a * b) ∧
    (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) = 2 / (1 + a * b) ↔ a = b) := by

  have h1 : 0 ≤ a * b := mul_nonneg ha hb

  have h2 : 1 - a * b > 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1),
      h, mul_nonneg ha hb]

  have h3 : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b) ≤ 0 := by
    have pos1 : 0 < (1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b) := by positivity
    have h4 : (1 + b ^ 2) * (1 + a * b) + (1 + a ^ 2) * (1 + a * b) - 2 * (1 + a ^ 2) * (1 + b ^ 2) ≤ 0 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1 / 2), h2, mul_nonneg ha hb, h]
    have h5 : 1 + a * b > 0 := by positivity
    have h6 : 1 + a ^ 2 > 0 := by positivity
    have h7 : 1 + b ^ 2 > 0 := by positivity
    have h8 : (1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b)) = 
        ((1 + b ^ 2) * (1 + a * b) + (1 + a ^ 2) * (1 + a * b) - 2 * (1 + a ^ 2) * (1 + b ^ 2)) 
        / ((1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b)) := by 
      field_simp [h6, h7, h5]
      <;> ring
    rw [h8]
    apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)

  constructor
  · -- Prove the inequality
    linarith only [show 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) ≤ 2 / (1 + a * b) by linarith [show 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b) ≤ 0 by linarith [h3]]]

  · -- Prove the equality condition
    constructor
    · -- Forward: if equality holds, then a = b
      intro heq
      have h3' : 1 / (1 + a ^ 2) + 1 / (1 + b ^ 2) - 2 / (1 + a * b) = 0 := by linarith

      have h8 : 0 < (1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b) := by positivity

      have heq' : ( (1 + b ^ 2) * (1 + a * b) + (1 + a ^ 2) * (1 + a * b) - 2 * (1 + a ^ 2) * (1 + b ^ 2) ) = 0 := by
        have h6 : 1 + a ^ 2 > 0 := by positivity
        have h7 : 1 + b ^ 2 > 0 := by positivity
        have h5 : 1 + a * b > 0 := by positivity
        have h8' : (1 + a ^ 2) * (1 + b ^ 2) * (1 + a * b) > 0 := by positivity
        field_simp [h6, h7, h5] at h3'
        nlinarith

      have h9 : (1 - a * b) * (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1 / 2), h2, mul_nonneg ha hb, h]

      cases' (mul_eq_zero.mp h9) with h10 h11
      · -- h10 : 1 - a * b = 0
        nlinarith [sq_nonneg (a + b - 2), h]
      · -- h11 : (a - b) ^ 2 = 0
        have h12 : a - b = 0 := by
          rw [sq_eq_zero_iff] at h11
          linarith
        linarith

    · -- Backward: if a = b, then equality holds
      intro heq
      rw [heq]
      have h4 : 1 - a * a > 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (2 * a - 2), h, mul_nonneg ha ha, sq_nonneg (a - b)]
      field_simp [show 0 < (1 + a ^ 2) * (1 + a ^ 2) * (1 + a * a) by positivity]
      nlinarith [sq_nonneg (a - 1), h4, mul_nonneg ha ha, h]