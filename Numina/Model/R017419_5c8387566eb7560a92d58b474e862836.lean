import Mathlib

open BigOperators Real Set

theorem inequalities_119290 (x : ℝ) :
  abs x ^ 3 - 2 * x ^ 2 - 4 * abs x + 3 < 0 ↔
  (x ∈ Ioo (-3) ((1 - sqrt 5) / 2) ∪ Ioo ((-1 + sqrt 5) / 2) 3) := by
  constructor
  · -- Assume abs x ^ 3 - 2 * x ^ 2 - 4 * abs x + 3 < 0, prove x ∈ Ioo (-3) ((1 - sqrt 5) / 2) ∪ Ioo ((-1 + sqrt 5) / 2) 3
    intro h
    have h1 : abs x ≥ 0 := abs_nonneg x
    have h3 : abs x ^ 3 - 2 * x ^ 2 - 4 * abs x + 3 = (abs x - 3) * (abs x ^ 2 + abs x - 1) := by
      have h21 : abs x ^ 2 = x ^ 2 := by
        cases le_or_lt 0 x with
        | inl h_nonneg =>
          rw [abs_of_nonneg h_nonneg]
          all_goals nlinarith
        | inr h_neg =>
          rw [abs_of_neg h_neg]
          nlinarith
      nlinarith [sq_nonneg (abs x ^ 2 - 1), sq_nonneg (x ^ 2 - 1)]
    have h4 : (abs x - 3) * (abs x ^ 2 + abs x - 1) < 0 := by
      linarith [h3, h]
    have h5 : abs x ^ 2 + abs x - 1 < 0 ∨ abs x ^ 2 + abs x - 1 > 0 := by
      by_contra h6
      push_neg at h6
      have h7 : abs x ^ 2 + abs x - 1 = 0 := by linarith
      have h8 : (abs x - 3) * (abs x ^ 2 + abs x - 1) = 0 := by
        rw [h7]
        norm_num
      linarith
    cases h5 with
    | inl h7 =>
      have h6 : abs x - 3 > 0 := by nlinarith
      nlinarith [abs_nonneg x, Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
    | inr h7 =>
      have h8 : abs x - 3 < 0 := by nlinarith
      have h10 : abs x < 3 := by linarith
      have h11 : abs x > (Real.sqrt 5 - 1) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      by_cases h3 : x ≥ 0
      · -- x ≥ 0
        have h4 : abs x = x := abs_of_nonneg h3
        have h5 : x > (Real.sqrt 5 - 1) / 2 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h6 : x < 3 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h7 : x ∈ Ioo ((-1 + sqrt 5) / 2) 3 := by
          constructor
  -- Show x > (-1 + sqrt 5) / 2
          · 
            nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  -- Show x < 3
          · 
            linarith
        right
        exact h7
      · -- x < 0
        have h4 : abs x = -x := abs_of_neg (show x < 0 by linarith)
        have h12 : -x > (Real.sqrt 5 - 1) / 2 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h13 : -x < 3 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h14 : x < (1 - Real.sqrt 5) / 2 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h15 : x > -3 := by
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h16 : x ∈ Ioo (-3) ((1 - sqrt 5) / 2) := by
          constructor
  -- Show x > -3
          · 
            linarith
  -- Show x < (1 - sqrt 5) / 2
          · 
            linarith
        left
        exact h16
  · -- Assume x ∈ Ioo (-3) ((1 - sqrt 5) / 2) ∪ Ioo ((-1 + sqrt 5) / 2) 3, prove abs x ^ 3 - 2 * x ^ 2 - 4 * abs x + 3 < 0
    intro h
    rcases h with (h1 | h2)
    · -- x ∈ (-3, (1 - sqrt 5) / 2)
      rcases h1 with ⟨h3, h4⟩
      have h31 : x < 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h4]
      have h32 : abs x = -x := abs_of_neg (show x < 0 by linarith)
      have h33 : abs x > (Real.sqrt 5 - 1) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h4]
      have h34 : abs x < 3 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h3]
      have h35 : abs x ^ 3 - 2 * x ^ 2 - 4 * abs x + 3 = (abs x - 3) * (abs x ^ 2 + abs x - 1) := by
        have h21 : abs x ^ 2 = x ^ 2 := by
          rw [abs_of_neg (show x < 0 by linarith)]
          nlinarith
        nlinarith [sq_nonneg (abs x ^ 2 - 1), sq_nonneg (x ^ 2 - 1)]
      have h36 : abs x ^ 2 + abs x - 1 > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h37 : abs x - 3 < 0 := by
        nlinarith
      have h38 : (abs x - 3) * (abs x ^ 2 + abs x - 1) < 0 := by
        apply mul_neg_of_neg_of_pos
  -- Show abs x - 3 < 0
        · linarith
  -- Show abs x ^ 2 + abs x - 1 > 0
        · nlinarith
      linarith [h35, h38]
    · -- x ∈ ((-1 + sqrt 5) / 2, 3)
      rcases h2 with ⟨h3, h4⟩
      have h41 : x > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h3]
      have h42 : abs x = x := abs_of_nonneg (show 0 ≤ x by linarith)
      have h43 : abs x > (Real.sqrt 5 - 1) / 2 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h3]
      have h44 : abs x < 3 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), h4]
      have h45 : abs x ^ 3 - 2 * x ^ 2 - 4 * abs x + 3 = (abs x - 3) * (abs x ^ 2 + abs x - 1) := by
        have h46 : abs x ^ 2 = x ^ 2 := by
          rw [abs_of_nonneg (show 0 ≤ x by linarith)]
          all_goals nlinarith
        nlinarith [sq_nonneg (abs x ^ 2 - 1), sq_nonneg (x ^ 2 - 1)]
      have h47 : abs x ^ 2 + abs x - 1 > 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 5 by norm_num), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      have h48 : abs x - 3 < 0 := by
        nlinarith
      have h49 : (abs x - 3) * (abs x ^ 2 + abs x - 1) < 0 := by
        apply mul_neg_of_neg_of_pos
  -- Show abs x - 3 < 0
        · linarith
  -- Show abs x ^ 2 + abs x - 1 > 0
        · nlinarith
      linarith [h45, h49]