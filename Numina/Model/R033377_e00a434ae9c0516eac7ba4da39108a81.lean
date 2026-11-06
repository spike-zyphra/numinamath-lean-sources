import Mathlib

open Real

theorem inequalities_178007 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (1 + a) * (1 + b) * (1 + c) ≥ 8 ∧
    ((1 + a) * (1 + b) * (1 + c) = 8 ↔ (a = b ∧ b = c)) := by
  constructor 
  · -- First part: proving the inequality $(1 + a) * (1 + b) * (1 + c) \geq 8$
    have h1 : (1 + a) * (1 + b) * (1 + c) = 1 + a + b + c + a * b + b * c + c * a + a * b * c := by
      ring
    rw [h1]
    have h2 : a * b * c = 1 := habc
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
              sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Prove the equality condition 
    constructor 
    · -- Forward direction: (1 + a) * (1 + b) * (1 + c) = 8 implies a = b ∧ b = c 
      intro h_eq
      have h1 : (1 + a) * (1 + b) * (1 + c) = 1 + a + b + c + a * b + b * c + c * a + a * b * c := by
        ring
      have h2 : a * b * c = 1 := habc 
      have h7 : (a - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h8 : a - 1 = 0 := by
        nlinarith
      have h4' : a = 1 := by linarith 
      have h9 : (b - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h10 : b - 1 = 0 := by 
        nlinarith 
      have h4b : b = 1 := by linarith 
      have h11 : (c - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
                  sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h12 : c - 1 = 0 := by 
        nlinarith 
      have h4c : c = 1 := by linarith 
      constructor 
      · -- Show a = b 
        nlinarith 
      · -- Show b = c 
        nlinarith 
    · -- Backward direction: a = b ∧ b = c implies (1 + a) * (1 + b) * (1 + c) = 8 
      rintro ⟨h1, h2⟩ 
      have h3 : c = a := by 
        linarith 
      have h4 : a * b * c = 1 := habc 
      have h5 : a * a * a = 1 := by 
        have h6 : a = b := h1 
        have h7 : b = c := h2 
        rw [show b = a by linarith, show c = a by linarith] at h4 
        nlinarith 
      have h6 : a ^ 3 = 1 := by 
        have h7 : a * a * a = 1 := h5 
        nlinarith 
      have h7 : a ^ 3 - 1 = 0 := by 
        nlinarith 
      have h8 : (a - 1) * (a ^ 2 + a + 1) = 0 := by 
        ring_nf at h7 ⊢ 
        linarith 
      cases' (mul_eq_zero.1 h8) with h9 h10 
      · -- Case a - 1 = 0, so a = 1 
        have h11 : a = 1 := by linarith 
        have h12 : b = 1 := by 
          have h6 : a = b := h1 
          nlinarith 
        have h13 : c = 1 := by 
          have h6 : b = c := h2 
          nlinarith 
        have h14 : (1 + a) * (1 + b) * (1 + c) = (1 + (1 : ℝ)) * (1 + (1 : ℝ)) * (1 + (1 : ℝ)) := by 
          rw [show a = (1 : ℝ) by linarith, show b = (1 : ℝ) by linarith, show c = (1 : ℝ) by linarith] 
        nlinarith 
      · -- Case a^2 + a + 1 = 0 
        have h14 : a ^ 2 + a + 1 > 0 := by 
          nlinarith [sq_nonneg (a + 1 / 2)]
        nlinarith [sq_nonneg (a ^ 2 + a + 1), h14]