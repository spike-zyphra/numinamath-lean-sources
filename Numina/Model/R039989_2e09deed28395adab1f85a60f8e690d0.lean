import Mathlib

theorem algebra_18880 :
    IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ x = (2 * a + 1 / (3 * b)) ^ 2 + (2 * b + 1 / (3 * c)) ^ 2 + (2 * c + 1 / (3 * a)) ^ 2} 8 := by
  constructor
  · -- Show 8 in in the set
    use Real.sqrt (6) / 6, Real.sqrt (6) / 6, Real.sqrt (6) / 6
    constructor
    · -- Show a > 0
      positivity
    constructor
    · -- Show b > 0
      positivity
    constructor
    · -- Show c > 0
      positivity
    · -- Show x = 8
      have h1 : (Real.sqrt 6 / 6 : ℝ) = Real.sqrt 6 / 6 := by rfl
      field_simp [h1, Real.sqrt_pos.2 (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      nlinarith [Real.sqrt_pos.2 (show (0 : ℝ) < (6 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg (6 : ℝ) ]
  · -- Show that 8 is minimal
    intro x h
    rcases h with ⟨a, b, c, ha, hb, hc, hx⟩
    have h1 : (2 * a + 1 / (3 * b)) ^ 2 ≥ 4 * (2 * a) * (1 / (3 * b)) := by 
      linarith [sq_nonneg (2 * a - 1 / (3 * b) ) ]
    have h2 : (2 * b + 1 / (3 * c)) ^ 2 ≥ 4 * (2 * b) * (1 / (3 * c)) := by 
      linarith [sq_nonneg (2 * b - 1 / (3 * c) ) ]
    have h3 : (2 * c + 1 / (3 * a)) ^ 2 ≥ 4 * (2 * c) * (1 / (3 * a)) := by 
      linarith [sq_nonneg (2 * c - 1 / (3 * a) ) ]
    have h4 : (2 * a + 1 / (3 * b)) ^ 2 + (2 * b + 1 / (3 * c)) ^ 2 + (2 * c + 1 / (3 * a)) ^ 2 ≥ 8 := by
      have h5 : (2 * a + 1 / (3 * b)) ^ 2 + (2 * b + 1 / (3 * c)) ^ 2 + (2 * c + 1 / (3 * a)) ^ 2 
          ≥ 4 * (2 * a) * (1 / (3 * b)) + 4 * (2 * b) * (1 / (3 * c)) + 4 * (2 * c) * (1 / (3 * a)) := by
        linarith [h1, h2, h3]
      have h6 : 4 * (2 * a) * (1 / (3 * b)) + 4 * (2 * b) * (1 / (3 * c)) + 4 * (2 * c) * (1 / (3 * a)) = (8 / 3) * (a / b + b / c + c / a) := by 
        field_simp 
        ring 
      have h7 : a / b + b / c + c / a ≥ 3 := by
        have h4 : a / b + b / c + c / a - 3 ≥ 0 := by
          have h8 : a / b + b / c + c / a - 3 = (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b - 3 * a * b * c) / (a * b * c) := by
            field_simp 
            ring 
          have h9 : a * b * c > 0 := by
            positivity 
          have h10 : a ^ 2 * c + b ^ 2 * a + c ^ 2 * b ≥ 3 * a * b * c := by
            nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
                sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                sq_nonneg (a * (a - b) + b * (b - c) + c * (c - a)), 
                sq_nonneg (a * b - b * c + c * a), mul_pos ha hb, mul_pos hb hc, mul_pos hc ha
              ]
          rw [h8] 
          apply div_nonneg 
          linarith
          positivity 
        linarith 
      linarith [h5, h6, h7]
    linarith [h4, hx]