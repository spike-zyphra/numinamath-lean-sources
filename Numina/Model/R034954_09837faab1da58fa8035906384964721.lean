import Mathlib

open Real

theorem inequalities_33637 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 ≥ a ^ 2 * b + b ^ 2 * c + c ^ 2 * d + d ^ 2 * a ∧
    (a ^ 3 + b ^ 3 + c ^ 3 + d ^ 3 = a ^ 2 * b + b ^ 2 * c + c ^ 2 * d + d ^ 2 * a ↔
      (a = b ∧ b = c ∧ c = d)) := by
  constructor
  · -- Prove the inequality.
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a), 
      sq_nonneg (a - c), sq_nonneg (b - d), 
        mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
          mul_pos hb hc, mul_pos hb hd, 
            mul_pos hc hd]
  · -- Prove the equality case.
    constructor
    · -- Forward: equality implies a = b = c = d
      intro heq
      have h1 : (a - b) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a), 
          sq_nonneg (a - c), sq_nonneg (b - d), 
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
              mul_pos hb hc, mul_pos hb hd, 
                mul_pos hc hd]
      have h2 : (b - c) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a), 
          sq_nonneg (a - c), sq_nonneg (b - d), 
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
              mul_pos hb hc, mul_pos hb hd, 
                mul_pos hc hd]
      have h3 : (c - d) ^ 2 = 0 := by
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - d), sq_nonneg (d - a), 
          sq_nonneg (a - c), sq_nonneg (b - d), 
            mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, 
              mul_pos hb hc, mul_pos hb hd, 
                mul_pos hc hd]
      have h4 : a - b = 0 := by
        rwa [sq_eq_zero_iff] at h1
      have h5 : b - c = 0 := by
        rwa [sq_eq_zero_iff] at h2
      have h6 : c - d = 0 := by
        rwa [sq_eq_zero_iff] at h3
      constructor
      · -- Show a = b
        linarith
      constructor
      · -- Show b = c
        linarith
      · -- Show c = d
        linarith
    · -- Backward: a = b = c = d implies equality
      rintro ⟨rfl, rfl, rfl⟩
      all_goals nlinarith