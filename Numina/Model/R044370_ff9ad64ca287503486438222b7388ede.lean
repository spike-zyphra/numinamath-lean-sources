import Mathlib

open Real

theorem inequalities_102568 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) ∧
    (3 / 2 = a / (b + c) + b / (c + a) + c / (a + b) ↔ a = b ∧ b = c) := by
  constructor
  · -- Prove the inequality
    have h1 : 0 < b + c := by nlinarith
    have h2 : 0 < c + a := by nlinarith
    have h3 : 0 < a + b := by nlinarith
    have h4 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
      have h1 : 0 < (b + c) * (c + a) * (a + b) := by positivity
      have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
        have h6 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
            ( (a * (c + a) * (a + b) ) + (b * (b + c) * (a + b) ) + (c * (b + c) * (c + a) ) - (3 / 2 * (b + c) * (c + a) * (a + b) ) ) / ( (b + c) * (c + a) * (a + b) ) := by
          field_simp
          ring
        rw [h6]
        apply div_nonneg
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a + b - c), sq_nonneg (a + c - b), sq_nonneg (b + c - a),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
        positivity
      linarith
    linarith 
  · -- Prove the equality
    constructor
    · -- Assume the equality, prove a = b ∧ b = c
      intro heq 
      have h1 : 0 < b + c := by nlinarith
      have h2 : 0 < c + a := by nlinarith
      have h3 : 0 < a + b := by nlinarith 
      field_simp [(show 0 < b + c by linarith), 
        (show 0 < c + a by linarith), (show 0 < a + b by linarith)] at heq
      have h7 : (a - b) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (mul_pos ha hb) hc
        ]
      have h7' : a - b = 0 := by 
        apply pow_eq_zero 
        exact h7 
      have h8 : a = b := by linarith
      have h10 : (b - c) ^ 2 = 0 := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          mul_pos (mul_pos ha hb) hc
        ]
      have h11 : b - c = 0 := by 
        apply pow_eq_zero 
        exact h10 
      have h12 : b = c := by linarith 
      constructor
      · exact h8 
      · exact h12 
    · -- Assume a = b ∧ b = c, prove the equality 
      rintro ⟨ha_eq, hb_eq⟩ 
      have ha1 : a = b := by
        linarith [ha_eq]
      have hb1 : b = c := by
        linarith [hb_eq]
      have ha7 : c = a := by
        nlinarith [ha1, hb1]
      have h1' : b + c = 2 * a := by 
        nlinarith [ha1, ha7] 
      have h2' : c + a = 2 * a := by 
        nlinarith [ha7, ha1] 
      have h3' : a + b = 2 * a := by 
        nlinarith [ha1] 
      have ha8 : a ≠ 0 := by 
        linarith 
      have eq2 : a / (b + c) = 1 / 2 := by 
        rw [show b + c = 2 * a by linarith [h1']]
        have h9 : a ≠ 0 := by
          linarith 
        field_simp [h9] 
        <;> nlinarith 
      have eq3 : b / (c + a) = 1 / 2 := by 
        rw [show c + a = 2 * a by linarith [h2']]
        have h9 : a ≠ 0 := by 
          linarith 
        field_simp [h9]
        <;> nlinarith 
      have eq4 : c / (a + b) = 1 / 2 := by 
        rw [show a + b = 2 * a by linarith [h3']]
        have h9 : a ≠ 0 := by 
          linarith 
        field_simp [h9]
        <;> nlinarith 
      linarith [eq2, eq3, eq4]