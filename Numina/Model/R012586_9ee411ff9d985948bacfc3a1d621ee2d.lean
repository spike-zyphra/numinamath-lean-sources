import Mathlib

theorem algebra_137279 {a b : ℝ} (ha : a ≠ b) (x : ℝ) (hx : x ≠ a ∧ x ≠ b) :
    (x - a) / (x - b) = (x - b) / (x - a) ↔ x = (a + b) / 2 := by
  constructor
  · -- Assume (x - a) / (x - b) = (x - b) / (x - a) holds, prove x = (a + b) / 2
    intro h
    have h1 : x - a ≠ 0 := by
      intro h_eq
      apply hx.1
      linarith
    have h2 : x - b ≠ 0 := by
      intro h_eq
      apply hx.2
      linarith
    have h3 : (x - a) ^ 2 = (x - b) ^ 2 := by 
      field_simp [(show x - b ≠ 0 by assumption), (show x - a ≠ 0 by assumption)] at h ⊢ 
      linarith 
    have : (x - a + (x - b)) * (x - a - (x - b)) = 0 := by 
      linarith [h3]
    have h5 : x - a + (x - b) = 0 ∨ x - a - (x - b) = 0 := by
      cases (mul_eq_zero.mp this) with
      | inl h6 => 
        left
        linarith 
      | inr h7 => 
        right 
        linarith 
    cases h5 with 
    | inl h6 => 
      have : x = (a + b) / 2 := by
        linarith 
      assumption 
    | inr h7 => 
      -- This case gives a = b, which is a contradiction
      have h8 : a = b := by
        nlinarith 
      have hne : a ≠ b := ha 
      contradiction 
  · -- Assume x = (a + b) / 2 prove $\frac{x-a}{x-b}=\frac{x-b}{x-a}$
    intro h_eq
    have h1 : x - a ≠ 0 := by 
      intro h_eq1
      have h2 : x = a := by linarith 
      tauto 
    have h2 : x - b ≠ 0 := by 
      intro h_eq1 
      have h3 : x = b := by linarith 
      tauto 
    have h3 : x - a = (b - a) / 2 := by 
      rw [show x = (a + b) / 2 by linarith [h_eq]] 
      linarith 
    have h4 : x - b = (a - b) / 2 := by 
      rw [show x = (a + b) / 2 by linarith [h_eq]] 
      linarith 
    rw [show (x - a) = (b - a) / 2 by linarith [h3]] 
    rw [show (x - b) = (a - b) / 2 by linarith [h4]] 
    have h5 : (b - a : ℝ) ≠ 0 := by 
      intro h_eq 
      have h7 : b - a = 0 := by 
        linarith 
      have h8 : a = b := by 
        linarith 
      have hne : a ≠ b := ha 
      contradiction 
    field_simp [(show (a - b : ℝ) ≠ 0 by 
      intro h_eq 
      have h7 : a - b = 0 := by 
        linarith 
      have h8 : a = b := by 
        linarith 
      have hne : a ≠ b := ha 
      contradiction 
    ), h5] 
    <;> nlinarith