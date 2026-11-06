import Mathlib

open Real

theorem inequalities_258937 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a + b + c + 2 = a * b * c) :
    (a + 1) * (b + 1) * (c + 1) ≥ 27 ∧ ((a + 1) * (b + 1) * (c + 1) = 27 ↔ a = 2 ∧ b = 2 ∧ c = 2) := by 
  have h1 : (a + 1) * (b + 1) * (c + 1) ≥ 27 := by 
    nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
      sq_nonneg (a * b - 4), sq_nonneg (b * c - 4), sq_nonneg (a * c - 4),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  constructor
  · exact h1
  · -- Equality holds if and only if a = b = c = 2
    constructor
    · -- Forward implication
      intro heq
      have h_eq1 : a * b * c = a + b + c + 2 := by linarith 
      have h_eq2 : (a - 2) * (b - 2) * (c - 2) = 0 := by
        nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), sq_nonneg (c - 2),
          sq_nonneg (a * b - 4), sq_nonneg (b * c - 4), sq_nonneg (a * c - 4),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      cases' (mul_eq_zero.mp h_eq2) with h_eq3 h_eq4
      cases' (mul_eq_zero.mp h_eq3) with h_eq3_1 h_eq3_2
      · -- h_eq3_1 : a - 2 = 0. Therefore, a = 2.
        have ha2 : a = 2 := by linarith 
        have h3 : 2 + b + c + 2 = 2 * b * c := by
          rw [show a = 2 by linarith] at h
          linarith 
        have h4 : (b - 2) * (c - 2) = 0 := by 
          nlinarith [sq_nonneg (b - 2), sq_nonneg (c - 2), 
            mul_pos hb hc
          ]
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- h5 : b - 2 = 0.
          have hb2 : b = 2 := by linarith 
          have hc2 : c = 2 := by
            nlinarith 
          constructor 
          · exact_mod_cast ha2
          constructor 
          · exact_mod_cast hb2
          · exact_mod_cast hc2
        · -- h6 : c - 2 = 0.
          have hc2 : c = 2 := by linarith 
          have hb2 : b = 2 := by
            nlinarith 
          constructor 
          · exact_mod_cast ha2
          constructor 
          · exact_mod_cast hb2
          · exact_mod_cast hc2
      · -- h_eq3_2 : b - 2 = 0.
        have hb2 : b = 2 := by linarith
        have h3 : a + 2 + c + 2 = a * 2 * c := by 
          rw [show b = 2 by linarith] at h 
          linarith 
        have h4 : (a - 2) * (c - 2) = 0 := by 
          nlinarith [sq_nonneg (a - 2), sq_nonneg (c - 2), 
            mul_pos ha hc
          ]
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- h5 : a - 2 = 0.
          have ha2 : a = 2 := by linarith 
          have hc2 : c = 2 := by 
            nlinarith 
          constructor 
          · exact_mod_cast ha2
          constructor 
          · exact_mod_cast hb2
          · exact_mod_cast hc2
        · -- h6 : c - 2 = 0.
          have hc2 : c = 2 := by linarith 
          have ha2 : a = 2 := by 
            nlinarith 
          constructor 
          · exact_mod_cast ha2
          constructor 
          · exact_mod_cast hb2
          · exact_mod_cast hc2
      · -- h_eq4 : c - 2 = 0.
        have hc2 : c = 2 := by linarith 
        have h3 : a + b + 2 + 2 = a * b * 2 := by
          rw [show c = 2 by linarith] at h 
          linarith 
        have h4 : (a - 2) * (b - 2) = 0 := by 
          nlinarith [sq_nonneg (a - 2), sq_nonneg (b - 2), 
            mul_pos ha hb
          ]
        cases' (mul_eq_zero.mp h4) with h5 h6
        · -- h5 : a - 2 = 0.
          have ha2 : a = 2 := by linarith 
          have hb2 : b = 2 := by 
            nlinarith 
          constructor 
          · exact_mod_cast ha2
          constructor 
          · exact_mod_cast hb2
          · exact_mod_cast hc2
        · -- h6 : b - 2 = 0.
          have hb2 : b = 2 := by linarith 
          have ha2 : a = 2 := by 
            nlinarith 
          constructor 
          · exact_mod_cast ha2
          constructor 
          · exact_mod_cast hb2
          · exact_mod_cast hc2
    · -- Backward implication
      rintro ⟨rfl, rfl, rfl⟩ 
      norm_num 
      all_goals nlinarith