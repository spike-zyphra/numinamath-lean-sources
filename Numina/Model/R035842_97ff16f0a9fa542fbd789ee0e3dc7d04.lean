import Mathlib
open Real

theorem algebra_1652 {a b : ℝ} (h : (2 * a + b) ^ 2 + abs (2 * a ^ 2 - 32) / sqrt (3 - a) = 0) (ha1 : sqrt (3 - a) ≠ 0) (ha2 : 3 - a > 0) : a = -4 ∧ b = 8 := by
  have h1 : (2 * a + b) ^ 2 ≥ 0 := by 
    apply sq_nonneg
  have h2 : abs (2 * a ^ 2 - 32) / sqrt (3 - a) ≥ 0 := by
    apply div_nonneg 
    · -- Show abs (2 * a ^ 2 - 32) ≥ 0
      apply abs_nonneg
    · -- Show sqrt (3 - a) ≥ 0 
      apply Real.sqrt_nonneg 
  have h3 : (2 * a + b) ^ 2 = 0 := by 
    linarith [h, h1, h2]
  have h4 : abs (2 * a ^ 2 - 32) / sqrt (3 - a) = 0 := by 
    linarith [h, h1, h2]
  -- From h4, we can derive that abs (2 * a ^ 2 - 32) = 0
  have h5 : abs (2 * a ^ 2 - 32) = 0 := by 
    have h6 : sqrt (3 - a) > 0 := by
      apply Real.sqrt_pos.2 
      linarith 
    have h7 : abs (2 * a ^ 2 - 32) = 0 := by 
      field_simp [show sqrt (3 - a) > 0 by assumption] at h4 ⊢ 
      <;> linarith
    exact h7
  -- Now from h5, we can derive that 2 * a ^ 2 - 32 = 0
  have h5' : 2 * a ^ 2 - 32 = 0 := by 
    rw [abs_eq_zero] at h5 
    linarith 
  -- From h5', we get a^2 = 16, so a = ±4
  have h8 : a ^ 2 = 16 := by 
    nlinarith 
  -- So a = ±4, but only a = -4 satisfies 3 - a > 0
  have ha3 : a = 4 ∨ a = -4 := by 
    have h2 : a ^ 2 - 16 = 0 := by 
      linarith 
    have h3 : (a - 4) * (a + 4) = 0 := by 
      linarith 
    cases (mul_eq_zero.1 h3) with 
    | inl h4 => 
      left 
      linarith 
    | inr h5 => 
      right 
      linarith 
  cases ha3 with 
  | inl h4a => 
    have h4b : 3 - a ≤ 0 := by 
      nlinarith 
    linarith 
  | inr h4a => 
    have h2a : 2 * a + b = 0 := by 
      have h9 : (2 * a + b) ^ 2 = 0 := by 
        linarith 
      have h10 : 2 * a + b = 0 := by 
        nlinarith 
      exact h10 
    have h4b : b = 8 := by 
      rw [show a = -4 by linarith [h4a]] at h2a 
      linarith 
    exact ⟨h4a, h4b⟩