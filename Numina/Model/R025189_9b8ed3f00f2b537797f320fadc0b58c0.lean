import Mathlib

open Real

theorem inequalities_115960 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1 / 8) :
    a^2 + b^2 + c^2 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ 15 / 16 ∧
    (a^2 + b^2 + c^2 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 = 15 / 16 ↔
      (a = b ∧ b = c)) := by
  constructor
  · -- First, we prove the inequality.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (c * a - 1 / 4),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  · -- Second, we prove the equality conditions
    constructor
    · -- Forward: If the expression equals 15/16, then a = b ∧ b = c 
      intro h
      have h1 : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - 1 / 4), sq_nonneg (b * c - 1 / 4), sq_nonneg (c * a - 1 / 4),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h31 : (a - b) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have ht1 : a - b = 0 := by 
        rw [sq_eq_zero_iff] at h31
        linarith
      have h32 : (b - c) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
      have ht2 : b - c = 0 := by 
        rw [sq_eq_zero_iff] at h32
        linarith
      constructor
      · -- a = b
        linarith
      · -- b = c
        linarith
    · -- Reverse: If (a = b ∧ b = c), then the expression equals 15/16
      rintro ⟨ha1, hb1⟩
      have h1 : a * b * c = 1 / 8 := habc
      have h2 : a = 1 / 2 := by
        have h11 : a = b := by linarith
        have h22 : b = c := by linarith
        have h3 : a * b * c = 1 / 8 := habc
        rw [show b = a by linarith [h11], show c = a by linarith [h11, h22]] at h3
        have h4 : a ^ 3 = 1 / 8 := by
          nlinarith
        have h5 : a = 1 / 2 := by
          have h6 : a ^ 3 - (1 / 8) = 0 := by linarith
          have h7 : (a - 1 / 2) * (a ^ 2 + a / 2 + 1 / 4) = 0 := by
            ring_nf at h6 ⊢
            nlinarith
          cases' (mul_eq_zero.mp h7) with h8 h9
          · -- First case
            linarith
          · -- Second case
            nlinarith [sq_nonneg (a + 1 / 2)]
        linarith
      have h9 : b = 1 / 2 := by linarith [ha1, h2]
      have h11 : c = 1 / 2 := by linarith [hb1, h9]
      rw [h2, h9, h11]
      nlinarith