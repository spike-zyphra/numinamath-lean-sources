import Mathlib

open Real

theorem algebra_279133 {a m n : ℝ} (ha : 0 < a) (hm : 0 < m) (hn : 0 < n) :
    (a > 1 → (a ^ m) ^ ((1 : ℝ) / n) > 1) ∧ (a < 1 → (a ^ m) ^ ((1 : ℝ) / n) < 1) := by 
  constructor
  · -- First implication: if a > 1, then (a ^ m) ^ ((1 : ℝ) / n) > 1
    intro ha1
    have h1 : (a ^ m) > (1 : ℝ) := by 
      apply Real.one_lt_rpow
      · linarith
      · linarith
    have h4 : ( (a ^ m) ^ ((1 : ℝ) / n) ) > ( (1 : ℝ) ^ ((1 : ℝ) / n) ) := by
      have h5 : (1 : ℝ) < (a ^ m) := by
        linarith [h1]
      have h3 : (1 : ℝ) / n > (0 : ℝ) := by
        apply div_pos
        · norm_num
        · linarith
      have h6 : ( (1 : ℝ) ^ ((1 : ℝ) / n) ) < ( (a ^ m) ^ ((1 : ℝ) / n) ) := by
        apply Real.rpow_lt_rpow
        all_goals
          try nlinarith [h1, show (0 : ℝ) < (1 : ℝ) / n by positivity, show (0 : ℝ) ≤ (1 : ℝ) by norm_num, show a ^ m > (0 : ℝ) by positivity]
      linarith 
    have h5 : ( (1 : ℝ) ^ ((1 : ℝ) / n) ) = (1 : ℝ) := by
      simp
    linarith [h5, h4]
  · -- Second direction: if a < 1, then $\sqrt[n]{a^m} < 1$
    intro ha2 
    have h1 : (a ^ m) < (1 : ℝ) := by 
      apply Real.rpow_lt_one 
      all_goals try linarith 
    have h2 : ((a ^ m) ^ ((1 : ℝ) / n)) < (1 : ℝ) := by
      have h3 : (1 : ℝ) / n > (0 : ℝ) := by
        apply div_pos 
        · norm_num 
        · linarith 
      have h4 : (a ^ m) > (0 : ℝ) := by 
        apply Real.rpow_pos_of_pos 
        all_goals try linarith
      have h5 : ( (a ^ m) ^ ((1 : ℝ) / n) ) < ( (1 : ℝ) ^ ((1 : ℝ) / n) ) := by
        apply Real.rpow_lt_rpow
        all_goals
          try nlinarith [h1, show (0 : ℝ) < (1 : ℝ) / n by positivity, show a ^ m > (0 : ℝ) by positivity, show (0 : ℝ) ≤ (1 : ℝ) by norm_num]
      have h6 : ( (1 : ℝ) ^ ((1 : ℝ) / n) ) = (1 : ℝ) := by 
        simp 
      linarith [h5, h6]
    exact h2