import Mathlib

open Real

theorem inequalities_114673 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a * b * c = 1 / 8) :
    15 / 16 ≤ a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + c ^ 2 * b ^ 2 ∧
    (15 / 16 = a ^ 2 + b ^ 2 + c ^ 2 + a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 + c ^ 2 * b ^ 2 ↔
      (a = b ∧ b = c)) := by

  constructor
  · -- First, we prove the inequality $15/16 \leq a^2 + b^2 + c^2 + a^2b^2 + a^2c^2 + b^2c^2$.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * b - 1 / 4), sq_nonneg (a * c - 1 / 4), sq_nonneg (b * c - 1 / 4),
          sq_nonneg (a - 1 / 2 : ℝ), sq_nonneg (b - 1 / 2 : ℝ), sq_nonneg (c - 1 / 2 : ℝ),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, mul_pos (mul_pos ha hb) hc]

  · -- Now, we prove the equality condition.
    constructor
    · -- Assume $15/16 = a^2 + b^2 + c^2 + a^2b^2 + a^2c^2 + b^2c^2$, prove $a = b \wedge b = c$.
      intro h_eq
      have h1 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * b - 1 / 4), sq_nonneg (a * c - 1 / 4), sq_nonneg (b * c - 1 / 4),
              sq_nonneg (a - 1 / 2 : ℝ), sq_nonneg (b - 1 / 2 : ℝ), sq_nonneg (c - 1 / 2 : ℝ),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (mul_pos ha hb) hc]

      have h2 : a - b = 0 := by
        nlinarith

      have h3 : a = b := by linarith

      have h4 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
              sq_nonneg (a * b - 1 / 4), sq_nonneg (a * c - 1 / 4), sq_nonneg (b * c - 1 / 4),
              sq_nonneg (a - 1 / 2 : ℝ), sq_nonneg (b - 1 / 2 : ℝ), sq_nonneg (c - 1 / 2 : ℝ),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, mul_pos (mul_pos ha hb) hc]

      have h5 : b - c = 0 := by
        nlinarith

      have h6 : b = c := by linarith

      exact ⟨h3, h6⟩

    · -- Assume $a = b \wedge b = c$, prove $15/16 = a^2 + b^2 + c^2 + a^2b^2 + a^2c^2 + b^2c^2$.
      rintro ⟨ha_eq, hb_eq⟩
      have ha2 : a = c := by
        nlinarith [ha_eq, hb_eq]

      have h1 : a ^ 3 = 1 / 8 := by
        have h3 : a * b * c = 1 / 8 := h
        rw [show b = a by linarith [ha_eq], show c = a by nlinarith [ha2]] at h3
        nlinarith

      have ha1 : a = 1 / 2 := by
        have h2 : a ^ 3 - 1 / 8 = 0 := by linarith

        have h3 : a ^ 3 - 1 / 8 = (a - 1 / 2) * (a ^ 2 + a / 2 + 1 / 4) := by
          ring

        rw [h3] at h2

        cases' (mul_eq_zero.1 h2) with h4 h5
        · 
          linarith
        · 
          have h6 : a ^ 2 + a / 2 + 1 / 4 > 0 := by
            nlinarith [sq_nonneg (a + 1 / 4)]
          nlinarith

      have hb1 : b = 1 / 2 := by
        nlinarith [ha1, ha_eq]

      have hc1 : c = 1 / 2 := by
        nlinarith [hb1, hb_eq, ha2]

      rw [ha1, hb1, hc1]
      nlinarith