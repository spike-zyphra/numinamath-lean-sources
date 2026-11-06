import Mathlib

open Real

theorem inequalities_161440 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : ℝ) (h_def : 1 / h = (1 / a + 1 / b + 1 / c) / 3) :
    h ≤ (a + b + c) / 3 ∧
    (h = (a + b + c) / 3 ↔ a = b ∧ b = c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc
  have eq1 : h = 3 * a * b * c / (a * b + b * c + c * a) := by
    have h2 : h ≠ 0 := by
        by_contra h0
        rw [h0] at h_def
        field_simp at h_def 
        <;> nlinarith
    field_simp at h_def ⊢
    nlinarith
  have h2 : h ≤ (a + b + c) / 3 := by
    rw [eq1]
    have pos1 : 0 < a * b + b * c + c * a := by
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    apply (div_le_iff₀ pos1).mpr
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h3 : h = (a + b + c) / 3 ↔ a = b ∧ b = c := by
    constructor
    · -- Forward implication: if h = (a + b + c) / 3, then a = b ∧ b = c
      intro heq
      rw [eq1] at heq
      have pos1 : 0 < a * b + b * c + c * a := by
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have eq1 : 9 * a * b * c = (a + b + c) * (a * b + b * c + c * a) := by
        field_simp at heq ⊢
        nlinarith
      have h4 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have h5 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
      have hab : a = b := by
        nlinarith
      have hbc : b = c := by
        nlinarith
      exact ⟨hab, hbc⟩
    · -- Reverse implication: if a = b ∧ b = c, then h = (a + b + c) / 3
      rintro ⟨rfl, rfl⟩
      rw [eq1]
      field_simp
      nlinarith
  constructor
  · exact h2
  · exact h3