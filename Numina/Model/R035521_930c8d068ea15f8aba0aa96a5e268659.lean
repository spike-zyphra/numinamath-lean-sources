import Mathlib

open Real

theorem number_theory_257168 :
    (Nat.floor ((sqrt 51 - 7) * 10^5)) / 10000 = (Nat.floor (sqrt 2 * 10^4)) / 10000 := by
  have h1 : Nat.floor ((sqrt 51 - 7) * (10 ^ 5 : ℝ)) = 14142 := by
    have h11 : 7 < sqrt 51 := by
      nlinarith [Real.sqrt_nonneg (51 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (51 : ℝ) by norm_num), sq_nonneg (sqrt 51 - 7)]
    have h12 : sqrt 51 < 8 := by
      nlinarith [Real.sqrt_nonneg (51 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (51 : ℝ) by norm_num)]
    have h13 : (sqrt 51 - 7) * (10 ^ 5 : ℝ) ≥ (14142 : ℝ) := by
      have h14 : sqrt 51 ≥ (7.14142 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (51 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (51 : ℝ) by norm_num), sq_nonneg (sqrt 51 - 7.14142)]
      linarith 
    have h14 : (sqrt 51 - 7) * (10 ^ 5 : ℝ) < (14143 : ℝ) := by
      have h15 : sqrt 51 < (7.14143 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (51 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (51 : ℝ) by norm_num), sq_nonneg (sqrt 51 - 7.14143)]
      linarith 
    have h15 : Nat.floor ((sqrt 51 - 7) * (10 ^ 5 : ℝ)) = 14142 := by 
      rw [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith
      all_goals
        try { 
          have h151 : (0 : ℝ) ≤ (sqrt 51 - 7) * (10 ^ 5 : ℝ) := by nlinarith [show (sqrt 51) ≥ (7: ℝ) by nlinarith [Real.sqrt_nonneg (51 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (51 : ℝ) by norm_num)]]
          all_goals nlinarith 
        }
        <;> try { tauto }
        all_goals try { nlinarith }
      all_goals norm_num 
      all_goals try { tauto }
      all_goals try { nlinarith }
    exact h15
  have h2 : Nat.floor (sqrt 2 * (10 ^ 4 : ℝ)) = 14142 := by
    have h1 : 1 < sqrt (2 : ℝ) := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h2 : sqrt (2 : ℝ) < 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h33 : sqrt (2 : ℝ) * (10 ^ 4 : ℝ) ≥ (14142 : ℝ) := by 
      have h4 : sqrt (2 : ℝ) ≥ (1.41421 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 - 1.41421)]
      linarith
    have h34 : sqrt (2 : ℝ) * (10 ^ 4 : ℝ) < (14143 : ℝ) := by
      have h5 : sqrt (2 : ℝ) < (1.41422 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sqrt 2 - 1.41422)]
      linarith
    have h15 : Nat.floor (sqrt 2 * (10 ^ 4 : ℝ)) = 14142 := by 
      rw [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try linarith 
      all_goals 
        try { 
          have h151 : (0 : ℝ) ≤ sqrt 2 * (10 ^ 4 : ℝ) := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
          all_goals nlinarith 
        }
      <;> try { tauto }
      all_goals try { nlinarith }
      all_goals norm_num 
      all_goals try { tauto }
      all_goals try { nlinarith }
    exact h15
  calc
    (Nat.floor ((sqrt 51 - 7) * (10 ^ 5 : ℝ))) / 10000 = 14142 / 10000 := by 
      rw [h1]
    _ = (Nat.floor (sqrt 2 * (10 ^ 4 : ℝ))) / 10000 := by 
      rw [h2]