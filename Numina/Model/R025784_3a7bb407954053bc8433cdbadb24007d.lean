import Mathlib

theorem inequalities_599606 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a * b + b * c + c * a = 1 / 3) :
    3 ≥ 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) +
        1 / (c ^ 2 - a * b + 1) := by
  have h12 : 0 < a ^ 2 - b * c + 1 := by
    nlinarith [sq_nonneg (a - b/2 - c/2), sq_nonneg (b - a/2 - c/2), sq_nonneg (c - a/2 - b/2), 
      h, mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc
    ]
  have h13 : 0 < b ^ 2 - c * a + 1 := by
    nlinarith [sq_nonneg (b - c/2 - a/2), sq_nonneg (c - b/2 - a/2), sq_nonneg (a - b/2 - c/2), 
      h, mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc
    ]
  have h14 : 0 < c ^ 2 - a * b + 1 := by
    nlinarith [sq_nonneg (c - a/2 - b/2), sq_nonneg (a - c/2 - b/2), sq_nonneg (b - c/2 - a/2), 
      h, mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc
    ]
  have h15 : 1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1) ≤ 3 := by
    have h17 : (1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1)) ≤ 3 := by 
      have h181 : 0 < (a ^ 2 - b * c + 1) := h12
      have h182 : 0 < (b ^ 2 - c * a + 1) := h13
      have h183 : 0 < (c ^ 2 - a * b + 1) := h14
      have hx84 : (1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1)) - (3 : ℝ) ≤ 0 := by
        have hx81 : 0 < (a ^ 2 - b * c + 1) * (b ^ 2 - c * a + 1) * (c ^ 2 - a * b + 1) := by positivity
        have hx83 : ( (1 / (a ^ 2 - b * c + 1) + 1 / (b ^ 2 - c * a + 1) + 1 / (c ^ 2 - a * b + 1)) - (3 : ℝ) ) = ( (b^2 - c * a + 1) * (c^2 - a * b + 1) + (a^2 - b * c + 1) * (c^2 - a * b + 1) + (a^2 - b * c + 1) * (b^2 - c * a + 1) - 3 * ((a^2 - b * c + 1) * (b^2 - c * a + 1) * (c^2 - a * b + 1)) ) / ( (a^2 - b * c + 1) * (b^2 - c * a + 1) * (c^2 - a * b + 1) ) := by 
          field_simp
          <;> ring
        rw [hx83] at *
        apply div_nonpos_of_nonpos_of_nonneg
        · -- To prove the numerator is ≤ 0 
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            mul_nonneg ha hb, mul_nonneg ha hc, 
            mul_nonneg hb hc, 
            mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ b * c by nlinarith), 
            mul_nonneg (show 0 ≤ a * b by nlinarith) (show 0 ≤ c * a by nlinarith), 
            mul_nonneg (show 0 ≤ b * c by nlinarith) (show 0 ≤ c * a by nlinarith), 
            h, mul_nonneg ha (show 0 ≤ a by linarith), 
            mul_nonneg hb (show 0 ≤ b by linarith), 
            mul_nonneg hc (show 0 ≤ c by linarith)
          ]
        all_goals positivity
      linarith
    linarith
  linarith [h15]