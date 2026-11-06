import Mathlib

open Real

theorem inequalities_114636 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (a + 1) * (b + 1) * (c + 1) = 8) :
    3 ≤ a + b + c ∧ ((a = b ∧ b = c) ↔ 3 = a + b + c) := by 
  constructor 
  · -- First part: prove 3 ≤ a + b + c 
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Second part: prove (a = b ∧ b = c) ↔ 3 = a + b + c
    constructor 
    · -- Forward: If ((a = b ∧ b = c) then (3 = a + b + c))
      intro h_eq 
      rcases h_eq with ⟨h1, h2⟩ 
      have h3 : a = b := h1 
      have h4 : b = c := h2 
      have h5 : a = c := by linarith 
      have h6 : a + b + c = 3 * a := by 
        linarith [h3, h4, h5]
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    · -- Backward: If (3 = a + b + c) then (a = b ∧ b = c)
      intro heq
      have ha1 : a + b + c = 3 := by linarith 
      have h3 : (a - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h4 : a - 1 = 0 := by 
        apply pow_eq_zero 
        exact h3
      have ha_eq : a = 1 := by 
        linarith 
      have h11 : (b - 1) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      have h12 : b - 1 = 0 := by 
        apply pow_eq_zero 
        exact h11 
      have hb_eq : b = 1 := by 
        linarith 
      have h13 : c = 1 := by 
        nlinarith [ha_eq, hb_eq, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc] 
      constructor <;> linarith