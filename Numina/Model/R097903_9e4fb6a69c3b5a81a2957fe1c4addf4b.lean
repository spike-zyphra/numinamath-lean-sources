import Mathlib

theorem algebra_322124 (x1 x2 k : ℝ) (hx1 : 0 < x1 ∧ x1 < 1) (hx2 : 1 < x2 ∧ x2 < 2)
    (hroots : 7 * x1 ^ 2 - (k + 13) * x1 + k ^ 2 - k - 2 = 0 ∧
      7 * x2 ^ 2 - (k + 13) * x2 + k ^ 2 - k - 2 = 0) :
    1 < x1 + x2 ∧ x1 + x2 < 3 ∧ 0 < x1 * x2 ∧ x1 * x2 < 2 ↔
    (3 - 2 * Real.sqrt 21) / 3 < k ∧ k < (3 + 2 * Real.sqrt 21) / 3 := by
  constructor
  · -- Forward direction: if the bounds on roots hold, then the bounds on k
    rintro ⟨h1, h2, h3, h4⟩
    have h_eq : k = 7 * (x1 + x2) - 13 := by
      have eq1 : 7 * x1 ^ 2 - (k + 13) * x1 + k ^ 2 - k - 2 = 0 := hroots.1
      have eq2 : 7 * x2 ^ 2 - (k + 13) * x2 + k ^ 2 - k - 2 = 0 := hroots.2
      have eq_subtract : 7 * x1 ^ 2 - 7 * x2 ^ 2 - (k + 13) * x1 + (k + 13) * x2 = 0 := by
        nlinarith
      have eq_diff : (x1 - x2) * (7 * (x1 + x2) - (k + 13)) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp eq_diff) with
      | inl h => 
        exfalso
        have : x1 < x2 := by linarith
        nlinarith
      | inr h => 
        linarith
    have hk1 : (3 - 2 * Real.sqrt 21) / 3 < k := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 21 by norm_num), Real.sq_sqrt (show 0 ≤ 21 by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < 21 by norm_num))]
    have hk2 : k < (3 + 2 * Real.sqrt 21) / 3 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 21 by norm_num), Real.sq_sqrt (show 0 ≤ 21 by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < 21 by norm_num))]
    constructor
    · -- Prove the lower bound
      nlinarith
    · -- Prove the upper bound
      nlinarith
  · -- Backward direction: if k is bounded, then the bounds on roots
    rintro ⟨hk1, hk2⟩
    have h_eq : k = 7 * (x1 + x2) - 13 := by
      have eq1 : 7 * x1 ^ 2 - (k + 13) * x1 + k ^ 2 - k - 2 = 0 := hroots.1
      have eq2 : 7 * x2 ^ 2 - (k + 13) * x2 + k ^ 2 - k - 2 = 0 := hroots.2
      have eq_subtract : 7 * x1 ^ 2 - 7 * x2 ^ 2 - (k + 13) * x1 + (k + 13) * x2 = 0 := by
        nlinarith
      have eq_diff : (x1 - x2) * (7 * (x1 + x2) - (k + 13)) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp eq_diff) with
      | inl h => 
        exfalso
        have : x1 < x2 := by linarith
        nlinarith
      | inr h => 
        linarith
    have hsum1 : 1 < x1 + x2 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 21 by norm_num), Real.sq_sqrt (show 0 ≤ 21 by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < 21 by norm_num))]
    have hsum2 : x1 + x2 < 3 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 21 by norm_num), Real.sq_sqrt (show 0 ≤ 21 by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < 21 by norm_num))]
    have hprod1 : 0 < x1 * x2 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 21 by norm_num), Real.sq_sqrt (show 0 ≤ 21 by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < 21 by norm_num))]
    have hprod2 : x1 * x2 < 2 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < 21 by norm_num), Real.sq_sqrt (show 0 ≤ 21 by norm_num), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < 21 by norm_num))]
    constructor
    · -- Prove the lower bound of the sum
      linarith
    constructor
    · -- Prove the upper bound of the sum
      linarith
    constructor
    · -- Prove the lower bound of the product
      linarith
    · -- Prove the upper bound of the product
      linarith