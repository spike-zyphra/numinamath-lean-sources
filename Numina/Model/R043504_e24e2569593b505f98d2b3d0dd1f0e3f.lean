import Mathlib

theorem inequalities_276884 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a * b * c = 1) (hrec : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by

  have h1 : 1 / a = b * c := by
    have h2 : a * (b * c) = 1 := by 
      calc
        a * (b * c) = a * b * c := by ring
        _ = 1 := by linarith [hsum]
    field_simp at *
    nlinarith

  have h2 : 1 / b = a * c := by 
    have h3 : b * (a * c) = 1 := by 
      calc 
        b * (a * c) = a * b * c := by ring 
        _ = 1 := by linarith [hsum]
    field_simp at *
    nlinarith

  have h3 : 1 / c = a * b := by
    have h4 : c * (a * b) = 1 := by 
      calc 
        c * (a * b) = a * b * c := by ring 
        _ = 1 := by linarith [hsum]
    field_simp at *
    nlinarith

  -- Substitute reciprocals into the inequality hrec
  have h4 : a + b + c > b * c + a * c + a * b := by
    rw [h1, h2, h3] at hrec
    nlinarith

  by_cases h5 : a > 1
  · -- Assume a > 1, need to show b ≤ 1 and c ≤ 1
    have h6 : b ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    have h7 : c ≤ 1 := by 
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
      ]
    left 
    constructor 
    · linarith 
    constructor 
    · linarith 
    · linarith 
  · -- Assume a ≤ 1
    have ha1 : a ≤ 1 := by linarith 
    by_cases h5b : b > 1 
    · -- Assume b > 1 
      have h8 : c ≤ 1 := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
      right 
      left 
      constructor 
      · linarith 
      constructor 
      · linarith 
      · linarith 
    · -- Assume b ≤ 1 
      have hb1 : b ≤ 1 := by linarith 
      have h8c : c > 1 := by 
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
        ]
      right 
      right 
      constructor 
      · linarith 
      constructor 
      · linarith 
      · linarith