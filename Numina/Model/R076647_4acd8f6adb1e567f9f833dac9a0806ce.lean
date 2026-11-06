import Mathlib

theorem algebra_95122 {a b : ℝ} (ha : a^2 + Real.pi^2 = 2 * Real.pi * a + 1) (hb : b^2 + Real.pi^2 = 2 * Real.pi * b + 1)
    (hne : a ≠ b) : |a - b| = 2 := by 
  have h1 : (a - Real.pi) ^ 2 = 1 := by
    nlinarith
  have h2 : (b - Real.pi) ^ 2 = 1 := by 
    nlinarith
  have h3 : a - Real.pi = 1 ∨ a - Real.pi = -1 := by 
    have : (a - Real.pi) ^ 2 = 1 := h1
    have h : (a - Real.pi) = 1 ∨ (a - Real.pi) = -1 := by
      rw [sq_eq_one_iff] at this
      tauto
    tauto
  have h4 : b - Real.pi = 1 ∨ b - Real.pi = -1 := by 
    have : (b - Real.pi) ^ 2 = 1 := h2
    have h : (b - Real.pi) = 1 ∨ (b - Real.pi) = -1 := by
      rw [sq_eq_one_iff] at this
      tauto 
    tauto

  cases h3 with 
  | inl h3l =>
    cases h4 with 
    | inl h4l =>
      -- Cases $a - \pi = 1$ and $b - \pi = 1$, which would imply $a = b$, contradicts $a ≠ b$
      exfalso 
      have : a = b := by 
        linarith [h3l, h4l]
      contradiction 
    | inr h4r => 
      -- Cases $a - \pi = 1$ and $b - \pi = -1$, so $a - b = 2$, and $|a - b| = 2$
      have h5 : a - b = 2 := by
        nlinarith 
      rw [h5]
      all_goals norm_num 
      all_goals nlinarith 
  | inr h3r => 
    cases h4 with 
    | inl h4l => 
      -- Cases $a - \pi = -1$ and $b - \pi = 1$, so $a - b = -2$, so $|a - b| = 2$
      have h5 : a - b = -2 := by
        nlinarith 
      rw [h5]
      all_goals norm_num 
    | inr h4r => 
      -- Cases $a - \pi = -1$ and $b - \pi = -1$, which would imply $a = b$, contradicts $a ≠ b$
      exfalso 
      have : a = b := by 
        linarith [h3r, h4r]
      contradiction
  all_goals linarith