import Mathlib

open Real

theorem inequalities_292483 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / c + c / b ≥ 4 * a / (a + b) ∧ (a / c + c / b = 4 * a / (a + b) ↔ a = c ∧ b = c) := by
  have h1 : 0 < a + b := by linarith
  constructor
  · -- Prove the inequality.
    have h2 : a / c + c / b - 4 * a / (a + b) ≥ 0 := by
      have h3 : 0 < a + b := by linarith
      have h4 : 0 < b * c * (a + b) := by
        apply mul_pos
        apply mul_pos
        all_goals nlinarith
      have h5 : (a / c + c / b - 4 * a / (a + b)) = (a * b * (a + b) + c^2 * (a + b) - 4 * a * b * c) / (b * c * (a + b)) := by
        field_simp
        ring
      rw [h5] at *
      apply div_nonneg
      nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c),
                sq_nonneg (a + b - c), sq_nonneg (c), sq_nonneg (a), sq_nonneg (b),
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
                ]
      all_goals positivity
    linarith
  · -- Prove the equality condition.
    constructor
    · -- Assume equality holds, prove a = c ∧ b = c.
      intro h
      have h1 : 0 < a + b := by linarith
      have h8 : a / c + c / b = 4 * a / (a + b) := by linarith
      have h4 : a * b * (a + b) + c^2 * (a + b) - 4 * a * b * c = 0 := by
        have h6 : a / c + c / b - 4 * a / (a + b) = 0 := by
          linarith
        have h5 : (a / c + c / b - 4 * a / (a + b)) = (a * b * (a + b) + c^2 * (a + b) - 4 * a * b * c) / (b * c * (a + b)) := by
          field_simp
          ring
        rw [h5] at h6
        have h9 : (b * c * (a + b) : ℝ) > 0 := by positivity
        have h10 : (a * b * (a + b) + c^2 * (a + b) - 4 * a * b * c) = 0 := by
          have h11 : (b * c * (a + b) : ℝ) > 0 := by positivity
          field_simp at h6 ⊢
          all_goals nlinarith
        linarith
      have h9 : (a - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h9a : a - c = 0 := by
        nlinarith
      have ha1 : a = c := by linarith
      have h10 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h10a : b - c = 0 := by
        nlinarith
      have hb1 : b = c := by linarith
      exact ⟨by linarith, by linarith⟩
    · -- Assume a = c ∧ b = c, prove equality holds.
      rintro ⟨ha1, hb1⟩
      have ha2 : a = c := by linarith
      have hb2 : b = c := by linarith
      have h1 : (a / c + c / b) = (4 * a / (a + b)) := by
        rw [show c = a by linarith [ha1, hb1], show b = a by linarith [hb1]]
        field_simp
        <;> nlinarith [sq_pos_of_pos ha, sq_nonneg (a - a)]
      linarith