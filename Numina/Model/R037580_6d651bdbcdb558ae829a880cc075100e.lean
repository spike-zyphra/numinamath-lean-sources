import Mathlib

theorem inequalities_82487 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    9 / (a + b + c) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ∧
    2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ≤ 1 / a + 1 / b + 1 / c := by
  constructor
  · -- Prove the first part: 9/(a+b+c) ≤ 2*(1/(a+b)+1/(b+c)+1/(c+a))
    have h1 : 0 < a + b + c := by linarith
    have h2 : 0 < a + b := by linarith
    have h3 : 0 < b + c := by linarith
    have h4 : 0 < c + a := by linarith
    have h5 : 9 / (a + b + c) ≤ 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) := by
      have h5 : 9 / (a + b + c) - 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ≤ 0 := by
        have pos' : 0 < (a + b + c) * (a + b) * (b + c) * (c + a) := by positivity
        have h5 : 9 / (a + b + c) - 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) =
            (9 * (a + b) * (b + c) * (c + a) - 2 * ((b + c) * (c + a) * (a + b + c) + (a + b) * (c + a) * (a + b + c) + (a + b) * (b + c) * (a + b + c)) ) / ((a + b + c) * (a + b) * (b + c) * (c + a)) := by
          field_simp
          ring
        rw [h5]
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Prove the numerator is ≤ 0
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
            sq_nonneg (b * (b - c)), sq_nonneg (b * (b - a)), 
            sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a + b by linarith) (show 0 < b + c by linarith), 
            mul_pos (show 0 < a + b by linarith) (show 0 < c + a by linarith), 
            mul_pos (show 0 < b + c by linarith) (show 0 < c + a by linarith)
          ]
        · -- Prove the denominator is ≥ 0
          positivity
      linarith
    exact h5
  · -- Prove the second part: 2*(1/(a+b)+1/(b+c)+1/(c+a)) ≤ 1/a+1/b+1/c
    have h1 : 0 < a := by assumption
    have h2 : 0 < b := by assumption
    have h3 : 0 < c := by assumption
    have h5 : 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) ≤ 1 / a + 1 / b + 1 / c := by
      have h5 : 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) - (1 / a + 1 / b + 1 / c) ≤ 0 := by
        have pos' : 0 < a * b * c * (a + b) * (b + c) * (c + a) := by positivity
        have h5 : 2 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) - (1 / a + 1 / b + 1 / c) =
            (2 * (a * b * c * (b + c) * (c + a) + a * b * c * (a + b) * (c + a) + a * b * c * (a + b) * (b + c)) - ( (b * c * (a + b) * (b + c) * (c + a) + a * c * (a + b) * (b + c) * (c + a) + a * b * (a + b) * (b + c) * (c + a)) ) ) / (a * b * c * (a + b) * (b + c) * (c + a)) := by
          field_simp
          ring
        rw [h5]
        apply div_nonpos_of_nonpos_of_nonneg
        · -- Prove the numerator is ≤ 0
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
            sq_nonneg (a * b), sq_nonneg (b * c), sq_nonneg (c * a),
            mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (show 0 < a * b by positivity) (show 0 < b * c by positivity), 
            mul_pos (show 0 < a * b by positivity) (show 0 < c * a by positivity), 
            mul_pos (show 0 < b * c by positivity) (show 0 < c * a by positivity)
          ]
        · -- Prove the denominator is ≥ 0
          positivity
      linarith
    exact h5