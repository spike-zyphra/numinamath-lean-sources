import Mathlib

open Set


theorem algebra_298848 (k : ℝ) :
    (∃ x1 x2 : ℝ, x1 ∈ Set.Ioo 0 1 ∧ x2 ∈ Set.Ioo 1 2 ∧
      7 * x1 ^ 2 - (k + 13) * x1 + k ^ 2 - k - 2 = 0 ∧
      7 * x2 ^ 2 - (k + 13) * x2 + k ^ 2 - k - 2 = 0) ↔
    -2 < k ∧ k < -1 ∨ 3 < k ∧ k < 4 := by
  constructor
  · -- Assume there exist two real roots in the specified intervals, prove the range of k
    rintro ⟨x1, x2, hx1, hx2, h1, h2⟩
    rcases hx1 with ⟨hx10, hx11⟩
    rcases hx2 with  ⟨hx21, hx22⟩
    have h3 : k ^ 2 - k - 2 > 0 := by
      nlinarith [sq_pos_of_pos (show 0 < x1 by linarith), sq_pos_of_pos (show 0 < 1 - x1 by linarith), 
        sq_pos_of_pos (show 0 < x2 - 1 by linarith), sq_pos_of_pos (show 0 < 2 - x2 by linarith)]
    have h4 : k ^ 2 - 2 * k - 8 < 0 := by
      nlinarith [sq_pos_of_pos (show 0 < x1 by linarith), sq_pos_of_pos (show 0 < 1 - x1 by linarith), 
        sq_pos_of_pos (show 0 < x2 - 1 by linarith), sq_pos_of_pos (show 0 < 2 - x2 by linarith)]
    have h5 : k ^ 2 - 3 * k > 0 := by
      nlinarith [sq_pos_of_pos (show 0 < x2 - 1 by linarith), sq_pos_of_pos (show 0 < 2 - x2 by linarith), 
        sq_pos_of_pos (show 0 < x1 by linarith), sq_pos_of_pos (show 0 < 1 - x1 by linarith)]
    have h6 : k < -1 ∨ k > 2 := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (k - 2), sq_nonneg (k + 1)]
    have h7 : -2 < k := by
      nlinarith [sq_nonneg (k - 4), sq_nonneg (k + 2)]
    have h8 : k < 4 := by
      nlinarith [sq_nonneg (k - 4), sq_nonneg (k + 2)]
    have h9 : k < 0 ∨ k > 3 := by
      by_contra h
      push_neg at h
      nlinarith [sq_nonneg (k - 0), sq_nonneg (k - 3)]
    rcases h6 with h6 | h6
    ·
      have hk1 : -2 < k := h7
      have hk2 : k < -1 := by linarith
      left
      constructor <;> linarith
    ·
      rcases h9 with h9 | h9
      ·
        linarith
      ·
        have hk3 : 3 < k := by linarith
        have hk4 : k < 4 := by linarith
        right
        constructor <;> linarith
  · -- Assume the range of k, prove the existence of the two real roots
    rintro (h | h)
    · -- When -2 < k < -1
      rcases h with  ⟨hk1, hk2⟩
      have h7 : (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) > 0 := by
        nlinarith [sq_nonneg (k - 3), sq_nonneg (k + 2)]
      have h9 : ∃ x1 : ℝ, x1 ∈ Set.Ioo 0 1 ∧ 7 * x1 ^ 2 - (k + 13) * x1 + k ^ 2 - k - 2 = 0 := by
        use ( (k + 13 - Real.sqrt ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2))) / 14 )
        constructor
        · -- Show x1 ∈ (0, 1)
          constructor
          · -- Show 0 < x1
            nlinarith [Real.sqrt_nonneg ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) by nlinarith)]
          · -- Show x1 < 1
            nlinarith [Real.sqrt_nonneg ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) by nlinarith)]
        · -- Show the equation
          nlinarith [Real.sqrt_nonneg ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) by nlinarith)]
      have h10 : ∃ x2 : ℝ, x2 ∈ Set.Ioo 1 2  ∧ 7 * x2 ^ 2 - (k + 13) * x2 + k ^ 2 - k - 2 = 0 := by
        use ( (k + 13 + Real.sqrt ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2))) / 14 )
        constructor
        · -- Show x2 ∈ (1, 2)
          constructor
          · -- Show 1 < x2
            nlinarith [Real.sqrt_nonneg ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) by nlinarith)]
          · -- Show x2 < 2
            nlinarith [Real.sqrt_nonneg ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) by nlinarith)]
        · -- Show the equation
          nlinarith [Real.sqrt_nonneg ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) by nlinarith)]
      rcases h9 with  ⟨x1, hx1, h1⟩
      rcases h10  with  ⟨x2, hx2, h2⟩
      exact ⟨x1, x2, hx1, hx2, h1, h2⟩
    · -- When 3 < k < 4
      rcases h  with  ⟨hk3, hk4⟩
      have h7 : (k + 13) ^ 2 - 28 * (k ^ 2 - k - 2) > 0  := by
        nlinarith [sq_nonneg (k - 3), sq_nonneg (k + 2)]
      have h9 : ∃ x1 : ℝ, x1 ∈ Set.Ioo 0 1  ∧ 7 * x1 ^ 2 - (k + 13) * x1 + k ^ 2 - k - 2 = 0  := by
        use ( (k + 13 - Real.sqrt ((k + 13) ^ 2 - 28 * (k ^ 2 - k - 2)))  / 14 )
        constructor
        · -- Show x1 ∈ (0, 1)
          constructor
          · -- Show 0  <  x1
            nlinarith [Real.sqrt_nonneg  ((k + 13)  ^  2 -  28  *  (k  ^  2  -  k  -  2)),  Real.sq_sqrt  (show  (0  :  ℝ)  ≤  (k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)  by  nlinarith)]
          · -- Show  x1  <  1
            nlinarith [Real.sqrt_nonneg  ((k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)),  Real.sq_sqrt  (show  (0  :  ℝ)  ≤  (k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)  by  nlinarith)]
        · --  Show  the  equation
          nlinarith [Real.sqrt_nonneg  ((k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)),  Real.sq_sqrt  (show  (0  :  ℝ)  ≤  (k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)  by  nlinarith)]
      have  h10  :  ∃  x2  :  ℝ,  x2  ∈  Set.Ioo  1  2  ∧  7  *  x2  ^  2  -  (k  +  13)  *  x2  +  k  ^  2  -  k  -  2  =  0  :=  by
        use  ( (k  +  13  +  Real.sqrt  ((k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)))  /  14  )
        constructor
        · --  Show  x2  ∈  (1,  2)
          constructor
          · --  Show  1  <  x2
            nlinarith  [Real.sqrt_nonneg  ((k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)),  Real.sq_sqrt  (show  (0  :  ℝ)  ≤  (k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)  by  nlinarith)]
          · --  Show  x2  <  2
            nlinarith  [Real.sqrt_nonneg  ((k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)),  Real.sq_sqrt  (show  (0  :  ℝ)  ≤  (k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)  by  nlinarith)]
        · --  Show  the  equation
          nlinarith  [Real.sqrt_nonneg  ((k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)),  Real.sq_sqrt  (show  (0  :  ℝ)  ≤  (k  +  13)  ^  2  -  28  *  (k  ^  2  -  k  -  2)  by  nlinarith)]
      rcases  h9  with  ⟨x1,  hx1,  h1⟩
      rcases  h10  with  ⟨x2,  hx2,  h2⟩
      exact  ⟨x1,  x2,  hx1,  hx2,  h1,  h2⟩