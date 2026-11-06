import Mathlib

theorem inequalities_182130 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hprod : a * b * c = 1) (h : a + b + c > 1 / a + 1 / b + 1 / c) :
    (a > 1 ∧ b ≤ 1 ∧ c ≤ 1) ∨ (b > 1 ∧ a ≤ 1 ∧ c ≤ 1) ∨ (c > 1 ∧ a ≤ 1 ∧ b ≤ 1) := by
  have h₁ : 1 / a = b * c := by
    field_simp
    nlinarith
  have h₂ : 1 / b = a * c := by
    field_simp
    nlinarith
  have h₃ : 1 / c = a * b := by
    field_simp
    nlinarith
  rw [h₁, h₂, h₃] at h
  by_cases ha1 : a > 1
  · -- Assume a > 1, then b ≤ 1 and c ≤ 1.
    have hb1 : b ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          hprod, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    have hc1 : c ≤ 1 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
          hprod, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
        ]
    left
    constructor
    · exact ha1
    constructor
    · exact hb1
    · exact hc1
  · -- Assume ¬(a > 1), i.e., a ≤ 1.
    by_cases hb1 : b > 1
    · -- Assume b > 1.
      have ha1' : a ≤ 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            hprod, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      have hc1' : c ≤ 1 := by
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            hprod, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]
      right
      left
      constructor
      · exact hb1
      constructor
      · exact ha1'
      · exact hc1'
    · -- Assume ¬(b > 1) and ¬(a > 1), i.e., b ≤ 1.
      by_cases hc1 : c > 1
      · -- Assume c > 1.
        have ha1' : a ≤ 1 := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
              hprod, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
            ]
        have hb1' : b ≤ 1 := by
          nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
              hprod, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
            ]
        right
        right
        constructor
        · exact hc1
        constructor
        · exact ha1'
        · exact hb1'
      · -- Assume ¬(c > 1), i.e., c ≤ 1.
        -- Then none of a, b, c are greater than 1.
        -- This is a contradiction.
        exfalso
        nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1), 
            hprod, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc
          ]