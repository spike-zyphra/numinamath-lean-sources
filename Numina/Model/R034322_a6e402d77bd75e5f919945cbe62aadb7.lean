import Mathlib

theorem inequalities_127194 (a b c : ℝ) (ha : 0 < a) 
      (hb : 0 < b) (hc : 0 < c) :
  3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) ∧
  a^3 + b^3 + c^3 + 1 / a + 1 / b + 1 / c ≥ 2 * (a + b + c) := by 
  constructor 
  · -- Prove the first inequality: $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b} \geqslant \frac{3}{2}$
    have h4 : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2 := by
      have h5 : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 ≥ 0 := by
        have pos1 : 0 < (b + c) := by positivity 
        have pos2 : 0 < (c + a) := by positivity 
        have pos3 : 0 < (a + b) := by positivity 
        have pos4 : 0 < (b + c) * (c + a) * (a + b) := by positivity 
        have h5_eq : a / (b + c) + b / (c + a) + c / (a + b) - 3 / 2 =
            ( 2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) ) / ( 2 * (b + c) * (c + a) * (a + b) ) := by 
          field_simp 
          ring 
        rw [h5_eq] at *
        have h6 : ( 2 * a * (c + a) * (a + b) + 2 * b * (b + c) * (a + b) + 2 * c * (b + c) * (c + a) - 3 * (b + c) * (c + a) * (a + b) ) ≥ 0 := by 
          nlinarith [ sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), 
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (a * (b - c)), 
            sq_nonneg (b * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (a - c)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc 
          ]
        apply div_nonneg 
        linarith 
        all_goals 
        positivity 
      linarith 
    linarith only [h4] 
  · -- Prove the second inequality: $a^3 + b^3 + c^3 + \frac{1}{a} + \frac{1}{b} + \frac{1}{c} \geqslant 2(a+b+c)$
    have h2 : a ^ 3 + 1 / a + (b ^ 3 + 1 / b + (c ^ 3 + 1 / c)) ≥ 2 * (a + b + c) := by 
      have h2a : a ^ 3 + 1 / a ≥ 2 * a := by 
        have ha1 : a > 0 := ha
        have h2a1 : a ^ 3 + 1 / a - 2 * a ≥ 0 := by 
          have h1 : a ^ 3 + 1 / a - 2 * a = (a ^ 4 + 1 - 2 * a ^ 2) / a := by 
            field_simp 
            ring 
          rw [h1] 
          have h4 : (a ^ 4 + 1 - 2 * a ^ 2) ≥ 0 := by 
            nlinarith [sq_nonneg (a ^ 2 - 1), sq_nonneg (a), mul_pos ha ha 
            ]
          have h6 : a > 0 := ha 
          apply div_nonneg 
          linarith 
          all_goals linarith 
        linarith
      have h2b : b ^ 3 + 1 / b ≥ 2 * b := by 
        have hb1 : b > 0 := hb
        have h2b1 : b ^ 3 + 1 / b - 2 * b ≥ 0 := by 
          have h1 : b ^ 3 + 1 / b - 2 * b = (b ^ 4 + 1 - 2 * b ^ 2) / b := by 
            field_simp 
            ring 
          rw [h1] 
          have h4 : (b ^ 4 + 1 - 2 * b ^ 2) ≥ 0 := by 
            nlinarith [sq_nonneg (b ^ 2 - 1), sq_nonneg (b), mul_pos hb hb 
            ]
          have h6 : b > 0 := hb 
          apply div_nonneg 
          linarith 
          all_goals linarith 
        linarith 
      have h2c : c ^ 3 + 1 / c ≥ 2 * c := by 
        have hc1 : c > 0 := hc 
        have h2c1 : c ^ 3 + 1 / c - 2 * c ≥ 0 := by 
          have h1 : c ^ 3 + 1 / c - 2 * c = (c ^ 4 + 1 - 2 * c ^ 2) / c := by 
            field_simp 
            ring 
          rw [h1] 
          have h4 : (c ^ 4 + 1 - 2 * c ^ 2) ≥ 0 := by 
            nlinarith [sq_nonneg (c ^ 2 - 1), sq_nonneg (c), mul_pos hc hc 
            ]
          have h6 : c > 0 := hc 
          apply div_nonneg 
          linarith 
          all_goals linarith 
        linarith 
      linarith [h2a, h2b, h2c] 
    linarith only [h2]