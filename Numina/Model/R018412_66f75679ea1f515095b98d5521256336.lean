import Mathlib

open Real

theorem algebra_264740 (a : ℕ → ℝ) (ha : a 0 = 1)
    (h : ∀ n, a (n + 1) = (2 ^ (1 / 2 : ℝ)) ^ a n) :
    Monotone a ∧ ∀ n, a n ≤ 2 := by

  have h1 : ∀ (n : ℕ), a n ≤ a (n + 1) := by 
    intro n 
    induction n with 
    | zero => 
      rw [ha]
      have h1' : a 1 = (2 ^ (1 / 2 : ℝ)) ^ (a 0) := h 0 
      rw [h1', ha]
      have : (2 ^ (1 / 2 : ℝ) : ℝ) ^ (1 : ℝ) > (1 : ℝ) := by 
        have h21 : (2 : ℝ) ^ (1 / 2 : ℝ) > (1 : ℝ) := by 
          have : (2 : ℝ) > (1 : ℝ) := by norm_num 
          have h31 : (2 : ℝ) ^ (1 / 2 : ℝ) > (1 : ℝ) ^ (1 / 2 : ℝ) := by 
            apply Real.rpow_lt_rpow 
            all_goals 
              linarith 
          have h24 : (1 : ℝ) ^ (1 / 2 : ℝ) = 1 := by 
            simp [Real.one_rpow]
          linarith [h24]
        norm_num at h21 ⊢ 
        all_goals
          linarith 
      linarith 
    | succ n ih => 
      have eq1 : a (n + 1) = (2 ^ (1 / 2 : ℝ)) ^ (a n) := h n 
      have eq2 : a (n + 2) = (2 ^ (1 / 2 : ℝ)) ^ (a (n + 1)) := h (n + 1)
      rw [eq2]
      have h45' : (2 ^ (1 / 2 : ℝ) : ℝ) > (1 : ℝ) := by
        have h51 : (2 : ℝ) ^ (1 / 2 : ℝ) > (1 : ℝ) := by 
          have : (2 : ℝ) > (1 : ℝ) := by norm_num 
          have h31 : (2 : ℝ) ^ (1 / 2 : ℝ) > (1 : ℝ) ^ (1 / 2 : ℝ) := by 
            apply Real.rpow_lt_rpow 
            all_goals 
              linarith 
          have h24 : (1 : ℝ) ^ (1 / 2 : ℝ) = 1 := by 
            simp [Real.one_rpow]
          linarith [h24]
        linarith 
      have h9k : (2 ^ (1 / 2 : ℝ) : ℝ) ^ (a n) ≤ (2 ^ (1 / 2 : ℝ) : ℝ) ^ (a (n + 1)) := by
        apply Real.rpow_le_rpow_of_exponent_le 
        all_goals
          nlinarith [show (2 : ℝ) ^ (1 / 2 : ℝ) > 1 by linarith [h45']]
      rw [eq1] at *
      all_goals 
        nlinarith [h9k] 

  have h2 : ∀ (n : ℕ), a n ≤ 2 := by
    intro n 
    induction n with 
    | zero => 
      rw [ha]
      norm_num
    | succ n ih => 
      have h1' : a (n + 1) = (2 ^ (1 / 2 : ℝ)) ^ a n := h n
      rw [h1']
      have h4 : (2 ^ (1 / 2 : ℝ) : ℝ) > (1 : ℝ) := by 
        have h51 : (2 : ℝ) ^ (1 / 2 : ℝ) > (1 : ℝ) := by 
          have : (2 : ℝ) > (1 : ℝ) := by norm_num 
          have h31 : (2 : ℝ) ^ (1 / 2 : ℝ) > (1 : ℝ) ^ (1 / 2 : ℝ) := by 
            apply Real.rpow_lt_rpow 
            all_goals 
              linarith 
          have h24 : (1 : ℝ) ^ (1 / 2 : ℝ) = 1 := by 
            simp [Real.one_rpow]
          linarith [h24]
        linarith 
      have h3 : a n ≤ (2 : ℝ) := ih 
      have h41 : (2 ^ (1 / 2 : ℝ) : ℝ) ^ a n ≤ (2 ^ (1 / 2 : ℝ) : ℝ) ^ (2 : ℝ) := by 
        apply Real.rpow_le_rpow_of_exponent_le 
        all_goals
          nlinarith [h4]
      have h51 : (2 ^ (1 / 2 : ℝ) : ℝ) ^ (2 : ℝ) = (2 : ℝ) := by 
        rw [← Real.rpow_mul]
        norm_num
        all_goals norm_num 
      have h42 : (2 ^ (1 / 2 : ℝ) : ℝ) ^ a n ≤ (2 : ℝ) := by 
        calc 
          (2 ^ (1 / 2 : ℝ) : ℝ) ^ a n ≤ (2 ^ (1 / 2 : ℝ) : ℝ) ^ (2 : ℝ) := h41 
          _ = (2 : ℝ) := h51 
      linarith [h42]

  constructor 
  · -- Show that `a` is monotone.
    apply monotone_nat_of_le_succ 
    intro n 
    specialize h1 n 
    simpa using h1 
  · -- Show that `a n ≤ 2` for all `n`.
    intro n 
    specialize h2 n 
    simpa using h2