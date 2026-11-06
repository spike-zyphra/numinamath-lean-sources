import Mathlib

open Real

theorem inequalities_292930 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) +
     a * b / (c ^ 2 + 2 * a * b)) ≤ 1 ∧
    1 ≤ (a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) +
        c ^ 2 / (c ^ 2 + 2 * a * b)) := by

  constructor
  · -- First inequality: $\frac{b c}{a^{2}+2 b c}+\frac{c a}{b^{2}+2 c a}+\frac{a b}{c^{2}+2 a b} \leq 1$
    have h1 : 0 < a * b * c := by 
      apply mul_pos
      apply mul_pos
      exact ha
      exact hb
      exact hc

    have h2 : b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) + a * b / (c ^ 2 + 2 * a * b) - 1 ≤ 0 := by
      have pos1 : 0 < a ^ 2 + 2 * b * c := by positivity
      have pos2 : 0 < b ^ 2 + 2 * c * a := by positivity
      have pos3 : 0 < c ^ 2 + 2 * a * b := by positivity
      have h3 : b * c / (a ^ 2 + 2 * b * c) + c * a / (b ^ 2 + 2 * c * a) + a * b / (c ^ 2 + 2 * a * b) - 1 = (b * c * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) + c * a * (a ^ 2 + 2 * b * c) * (c ^ 2 + 2 * a * b) + a * b * (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) - (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) / ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) := by
        field_simp
        ring
      rw [h3] at *
      have pos4 : (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) > 0 := by positivity
      have h4 : b * c * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) + c * a * (a ^ 2 + 2 * b * c) * (c ^ 2 + 2 * a * b) + a * b * (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) - (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) ≤ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
            mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
            mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity)
        ]
      apply div_nonpos_of_nonpos_of_nonneg h4 (by positivity)
    linarith

  · -- Second inequality: $1 \leq \frac{a^2}{a^2+2 b c}+\frac{b^2}{b^2+2 c a}+\frac{c^2}{c^2+2 a b}$
    have h3 : a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) - 1 ≥ 0 := by
      have pos1 : 0 < a ^ 2 + 2 * b * c := by positivity
      have pos2 : 0 < b ^ 2 + 2 * c * a := by positivity
      have pos3 : 0 < c ^ 2 + 2 * a * b := by positivity
      have h1 : a ^ 2 / (a ^ 2 + 2 * b * c) + b ^ 2 / (b ^ 2 + 2 * c * a) + c ^ 2 / (c ^ 2 + 2 * a * b) - 1 = (a ^ 2 * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) + b ^ 2 * (a ^ 2 + 2 * b * c) * (c ^ 2 + 2 * a * b) + c ^ 2 * (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) - (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) / ((a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b)) := by 
        field_simp
        ring
      rw [h1] at *
      have pos4 : (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) > 0 := by positivity
      have h2 : a ^ 2 * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) + b ^ 2 * (a ^ 2 + 2 * b * c) * (c ^ 2 + 2 * a * b) + c ^ 2 * (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) - (a ^ 2 + 2 * b * c) * (b ^ 2 + 2 * c * a) * (c ^ 2 + 2 * a * b) ≥ 0 := by
        nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b by positivity) (show 0 < a * c by positivity), 
            mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
            mul_pos (show 0 < a * c by positivity) (show 0 < b * c by positivity)
        ]
      apply div_nonneg h2 (by positivity)
    linarith