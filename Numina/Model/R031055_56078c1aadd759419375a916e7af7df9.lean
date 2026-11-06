import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_254532 :
    {x : ℝ | logb (1/3) (x^2 - 6*x + 18) - 2*logb (1/3) (x - 4) < 0 ∧ 
      x^2 - 6*x + 18 > 0 ∧ x - 4 > 0
    } = Set.Ioi 4 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ioi]
  constructor
  · -- First, prove that if x is in the left side set, then x ∈ (4, +∞)
    rintro ⟨h, h1, h2⟩
    have : x > 4 := by linarith 
    linarith 
  · -- Second, prove that if x ∈ (4, +∞), then x is in the left side set
    intro h
    have hx4 : x > 4 := by linarith
    constructor
    · -- Show the main inequality
      have h1 : x ^ 2 - 6 * x + 18 > (0 : ℝ) := by
        nlinarith [sq_nonneg (x - 3)]
      have h2 : x - 4 > (0 : ℝ) := by linarith 
      have h3 : (x ^ 2 - 6 * x + 18 : ℝ) > 0 := by
        nlinarith [sq_nonneg (x - 3)]
      have h4 : (x - 4 : ℝ) > 0 := by linarith 
      have h6 : logb (1 / 3) (x^2 - 6 * x + 18) - 2 * logb (1 / 3) (x - 4) = logb (1 / 3) ((x ^ 2 - 6 * x + 18) / (x - 4) ^ 2) := by
        have h7 : 2 * logb (1 / 3) (x - 4) = logb (1 / 3) ((x - 4) ^ 2) := by 
          simp [logb_pow]
        have h8 : logb (1 / 3) (x^2 - 6 * x + 18) - 2 * logb (1 / 3) (x - 4) = logb (1 / 3) (x^2 - 6 * x + 18) - logb (1 / 3) ((x - 4) ^ 2) := by 
          rw [h7]
        rw [h8]
        rw [logb_div (by positivity) (by positivity)]
      rw [h6]
      have h7 : (x ^ 2 - 6 * x + 18 : ℝ) / (x - 4) ^ 2 > (1 : ℝ) := by 
        apply (lt_div_iff₀ (by positivity)).mpr
        nlinarith [sq_pos_of_pos (show 0 < (x - 4 : ℝ) by linarith), sq_nonneg (x - 3)]
      have h8 : logb (1 / 3) ((x ^ 2 - 6 * x + 18) / (x - 4) ^ 2) < (0 : ℝ) := by 
        have h9 : logb (1 / 3) ((x ^ 2 - 6 * x + 18) / (x - 4) ^ 2) < logb (1 / 3) (1 : ℝ) := by 
          apply Real.logb_lt_logb_of_base_lt_one 
          all_goals 
            try norm_num 
            try linarith [h7]
        have h10 : logb (1 / 3) (1 : ℝ) = 0 := by 
          norm_num [logb_one]
        linarith [h9, h10]
      linarith 
    constructor 
    · -- Show x^2 - 6*x + 18 > 0 
      nlinarith [sq_nonneg (x - 3)]
    · -- Show x - 4 > 0 
      linarith