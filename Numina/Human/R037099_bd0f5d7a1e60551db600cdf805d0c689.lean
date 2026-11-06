import Mathlib

open Real

theorem inequalities_124969 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c ≤ 3) :
    a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 3 / 2 ∧
    3 / 2 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) := by
  constructor
  · -- We need to prove a / (1 + a ^ 2) + b / (1 + b ^ 2) + c / (1 + c ^ 2) ≤ 3 / 2
    have h1 : a / (1 + a ^ 2) ≤ 1 / 2 := by
      have h1 : a ≥ 0 := ha
      have h2 : 1 + a ^ 2 > 0 := by
        suffices 1 + a ^ 2 ≥ 1 by linarith
        nlinarith [sq_nonneg a]
      have h3 : a / (1 + a ^ 2) ≤ 1 / 2 := by
        have h4 : a / (1 + a ^ 2) ≤ (1 / 2) := by
          have h5 : a * 2 ≤ (1 + a ^ 2) := by
            nlinarith [sq_nonneg (a - 1)]
          apply (div_le_iff₀ h2).mpr
          linarith
        linarith
      exact h3
    have h2 : b / (1 + b ^ 2) ≤ 1 / 2 := by
      have h1 : b ≥ 0 := hb
      have h2 : 1 + b ^ 2 > 0 := by
        suffices 1 + b ^ 2 ≥ 1 by linarith
        nlinarith [sq_nonneg b]
      have h3 : b / (1 + b ^ 2) ≤ 1 / 2 := by
        have h4 : b / (1 + b ^ 2) ≤ (1 / 2) := by
          have h5 : b * 2 ≤ (1 + b ^ 2) := by
            nlinarith [sq_nonneg (b - 1)]
          apply (div_le_iff₀ h2).mpr
          linarith
        linarith
      exact h3
    have h3 : c / (1 + c ^ 2) ≤ 1 / 2 := by
      have h1 : c ≥ 0 := hc
      have h2 : 1 + c ^ 2 > 0 := by
        suffices 1 + c ^ 2 ≥ 1 by linarith
        nlinarith [sq_nonneg c]
      have h3 : c / (1 + c ^ 2) ≤ 1 / 2 := by
        have h4 : c / (1 + c ^ 2) ≤ (1 / 2) := by
          have h5 : c * 2 ≤ (1 + c ^ 2) := by
            nlinarith [sq_nonneg (c - 1)]
          apply (div_le_iff₀ h2).mpr
          linarith
        linarith
      exact h3
    linarith
  · -- We need to prove 3 / 2 ≤ 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c)
    have h4 : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) ≥ 3 / 2 := by
      have h5 : ∀ x : ℝ, 0 ≤ x ∧ x ≤ 3 → 1 / (1 + x) ≥ (3 - x) / 4 := by
        intro x h
        rcases h with ⟨hx1, hx2⟩
        have h1 : 1 + x > 0 := by linarith
        have h2 : 1 / (1 + x) - (3 - x) / 4 ≥ 0 := by
          have h3 : (3 - x) / 4 = (3 - x) / 4 := rfl
          have h4 : 1 / (1 + x) - (3 - x) / 4 = (x - 1) ^ 2 / (4 * (1 + x)) := by
            field_simp
            ring
          rw [h4]
          have h5 : (x - 1) ^ 2 ≥ 0 := sq_nonneg (x - 1)
          have h6 : 4 * (1 + x) > 0 := by nlinarith
          exact div_nonneg h5 (by linarith)
        linarith [h2]
      have h6 := h5 a ⟨ha, by linarith [h, ha, hb, hc]⟩
      have h7 := h5 b ⟨hb, by linarith [h, ha, hb, hc]⟩
      have h8 := h5 c ⟨hc, by linarith [h, ha, hb, hc]⟩
      have h9 : (3 - a) / 4 + (3 - b) / 4 + (3 - c) / 4 ≥ 3 / 2 := by
        linarith [sq_nonneg (a + b + c - 3), h]
      linarith [h6, h7, h8, h9]
    linarith [h4]