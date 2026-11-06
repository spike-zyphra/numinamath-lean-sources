import Mathlib

open Real

theorem inequalities_293457 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    a + b^2 + b / a ≥ 3 * b ∧ (a + b^2 + b / a = 3 * b ↔ a = 1 ∧ b = 1) := by
  have h1 : a + b^2 + b / a - 3 * b ≥ 0 := by
    have h2 : a + b^2 + b / a - 3 * b = (a ^ 2 + a * b ^ 2 - 3 * a * b + b) / a := by
      field_simp
      ring
    rw [h2] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a * b - 1), 
      sq_nonneg (a * (b - 1)), sq_nonneg ((b - 1) * a), 
      mul_pos ha hb, mul_pos ha (show 0 < b ^ 2 by nlinarith), mul_pos (show 0 < b ^ 2 by nlinarith) ha
    ]
    all_goals linarith
  have h3 : a + b^2 + b / a ≥ 3 * b := by linarith
  constructor
  · -- First part: the inequality.
    linarith
  · -- Second part: the equality.
    constructor
    · -- Assume equality holds, prove a = 1 ∧ b = 1.
      intro heq
      have h_eq : a + b^2 + b / a - 3 * b = 0 := by
        linarith
      have h_eq1 : (a ^ 2 + a * b ^ 2 - 3 * a * b + b) / a = 0 := by
        have h2 : a + b^2 + b / a - 3 * b = (a ^ 2 + a * b ^ 2 - 3 * a * b + b) / a := by
          field_simp
          ring
        rw [h2] at h_eq
        linarith
      have h_eq2 : a ^ 2 + a * b ^ 2 - 3 * a * b + b = 0 := by
        have h4 : 0 < a := ha
        have h7 : a ^ 2 + a * b ^ 2 - 3 * a * b + b = 0 := by
          have : (a ^ 2 + a * b ^ 2 - 3 * a * b + b) / a = (a ^ 2 + a * b ^ 2 - 3 * a * b + b) / a := rfl
          field_simp at h_eq1 ⊢
          <;> nlinarith
        linarith
      have h_eq3 : (a - 1) ^ 2 + (b - 1) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a * b - 1), sq_nonneg (a - b), sq_nonneg (a * (b - 1)), sq_nonneg ((b - 1) * a),
          mul_pos ha hb, mul_pos ha (show 0 < b ^ 2 by nlinarith), mul_pos (show 0 < b ^ 2 by nlinarith) ha
        ]
      have h_eq31 : (a - 1) ^ 2 = 0 := by
        nlinarith [h_eq3]
      have h_eq32 : (b - 1) ^ 2 = 0 := by
        nlinarith [h_eq3]
      have h_eq311 : a - 1 = 0 := by
        apply pow_eq_zero 
        exact h_eq31
      have h_eq321 : b - 1 = 0 := by
        apply pow_eq_zero 
        exact h_eq32
      constructor
      · -- Show that a = 1
        linarith 
      · -- Show that b = 1
        linarith 
    · -- Assume a = 1 ∧ b = 1, prove equality.
      rintro ⟨ha1, hb1⟩
      rw [ha1, hb1]
      norm_num