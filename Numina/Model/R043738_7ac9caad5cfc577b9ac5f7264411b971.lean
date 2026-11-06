import Mathlib

theorem inequalities_67173 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 1) :
    (∃ x y z, x = a - a * b ∧ y = b - b * c ∧ z = c - c * a ∧
      x ≤ 1 / 4 ∨ y ≤ 1 / 4 ∨ z ≤ 1 / 4 ∧
      x ≥ 2 / 9 ∨ y ≥ 2 / 9 ∨ z ≥ 2 / 9) := by
  have h1 : a - a * b ≤ 1 / 4 ∨ b - b * c ≤ 1 / 4 ∨ c - c * a ≤ 1 / 4 := by 
    by_cases h5 : a - a * b ≤ 1 / 4
    · -- Assume first expression is ≤ 1/4, so the disjunction is satisfied
      left
      linarith
    · -- Assume a - a * b > 1/4
      by_cases h6 : b - b * c ≤ 1 / 4
      · -- Assume second expression is ≤ 1/4, so the disjunction is satisfied
        right
        left
        linarith
      · -- Assume both a - a * b > 1/4 and b - b * c > 1/4
        right
        right
        -- We need to show the third expression must be ≤ 1/4
        nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  
  have h2 : a - a * b ≥ 2 / 9 ∨ b - b * c ≥ 2 / 9 ∨ c - c * a ≥ 2 / 9 := by 
    by_cases h6 : a - a * b ≥ 2 / 9
    · -- Assume first expression is ≥ 2/9, so the disjunction is satisfied
      left
      linarith
    · -- Assume a - a * b < 2/9
      by_cases h7 : b - b * c ≥ 2 / 9
      · -- Assume second expression is ≥ 2/9, so the disjunction is satisfied
        right
        left
        linarith
      · -- Assume both a - a * b < 2/9 and b - b * c < 2/9
        right
        right
        -- We need to show the third expression must be ≥ 2/9
        nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]

  refine' ⟨a - a * b, b - b * c, c - c * a, _⟩
  norm_num at *
  all_goals 
    try { 
      tauto
    }
    <;> try { 
      rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;> 
      try { 
        tauto
      }
    }
    <;> try { 
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), sq_nonneg (c - 1 / 2), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    }