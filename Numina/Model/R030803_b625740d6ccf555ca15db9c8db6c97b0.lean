import Mathlib

open Real

theorem inequalities_104828 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c * (a + b + c) = 3) :
    8 ≤ (a + b) * (b + c) * (c + a) ∧
    (8 = (a + b) * (b + c) * (c + a) ↔ a = b ∧ b = c) := by
  constructor
  · -- Forward: $8 \leq (a + b) \cdot (b + c) \cdot (c + a)$
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]
  · -- Backward: $8 = (a + b) \cdot (b + c) \cdot (c + a) \implies a = b \wedge b = c$
    constructor
    · -- Forward: if $8 = (a + b) \cdot (b + c) \cdot (c + a)$, then $a = b \wedge b = c$.
      intro heq
      have h1 : (a + b) * (b + c) * (c + a) = 8 := by linarith
      have h2 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]
      have hab : a = b := by
        nlinarith
      have h3 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]
      have hbc : b = c := by
        nlinarith
      exact ⟨hab, hbc⟩
    · -- Backward: if $a = b \wedge b = c$, then $8 = (a + b) \cdot (b + c) \cdot (c + a)$.
      rintro ⟨rfl, rfl⟩
      -- Substitute $a = b = c$ into the constraint and compute.
      have h3 : a ^ 4 = 1 := by
        have h2 : a * a * a * (a + a + a) = 3 := by
          nlinarith
        nlinarith
      have h4 : a > 0 := by nlinarith
      have h5 : a = 1 := by
        have h6 : a ^ 4 = 1 := h3
        have h7 : a ^ 2 = 1 := by
          have h8 : (a ^ 2) ^ 2 = 1 := by
            nlinarith
          have h9 : a ^ 2 ≥ 0 := sq_nonneg (a)
          have h10 : a ^ 2 = 1 := by
            have h11 : (a ^ 2) ^ 2 - 1 = 0 := by
              nlinarith
            have h12 : (a ^ 2 - 1) * (a ^ 2 + 1) = 0 := by
              nlinarith
            cases' (mul_eq_zero.mp h12) with h13 h14
            · -- a^2 - 1 = 0
              linarith
            · -- a^2 + 1 = 0
              nlinarith [sq_nonneg (a ^ 2)]
          linarith
        have h8 : a ≥ 0 := by linarith
        have h9 : a = 1 := by
          have h10 : a ^ 2 - 1 = 0 := by
            nlinarith
          have h11 : (a - 1) * (a + 1) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h11) with h12 h13
          · -- a - 1 = 0
            linarith
          · -- a + 1 = 0
            nlinarith
        linarith
      rw [show a = 1 by linarith]
      norm_num