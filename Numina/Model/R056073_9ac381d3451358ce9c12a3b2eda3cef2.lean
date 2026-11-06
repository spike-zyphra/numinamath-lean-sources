import Mathlib

theorem algebra_188179 (x : ℝ) (hx : x > 4) :
    0.1 * Real.logb 2 (x - 4) ^ 4 - 1.3 * Real.logb 2 (x - 4) ^ 2 + 3.6 = 0 ↔
    x = 17 / 4 ∨ x = 33 / 8 ∨ x = 8 ∨ x = 12 := by
  constructor
  · -- Forward direction: proving the equation implies the solutions
    intro h
    have h1 : Real.logb 2 (x - 4) ^ 4 - 13 * Real.logb 2 (x - 4) ^ 2 + 36 = 0 := by
      ring_nf at h ⊢
      nlinarith
    have h2 : Real.logb 2 (x - 4) ^ 4 - 13 * Real.logb 2 (x - 4) ^ 2 + 36 = 
          (Real.logb 2 (x - 4) ^ 2 - 9) * (Real.logb 2 (x - 4) ^ 2 - 4) := by
      ring
    rw [h2] at h1
    cases' (mul_eq_zero.1 h1) with h3 h4
    · -- Case where $\log_2(x-4)^2 = 9$
      have h5 : Real.logb 2 (x - 4) ^ 2 = 9 := by linarith
      have h6 : Real.logb 2 (x - 4) = 3 ∨ Real.logb 2 (x - 4) = -3 := by
        have h7 : Real.logb 2 (x - 4) ^ 2 - 9 = 0 := by linarith
        have h8 : Real.logb 2 (x - 4) ^ 2 - 9 = (Real.logb 2 (x - 4) - 3) * (Real.logb 2 (x - 4) + 3) := by ring
        rw [h8] at h7
        cases' (mul_eq_zero.1 h7) with h9 h10
        · -- Real.logb 2 (x - 4) - 3 = 0
          left
          linarith
        · -- Real.logb 2 (x - 4) + 3 = 0
          right
          linarith
      cases' h6 with h6 h6
      · -- Real.logb 2 (x - 4) = 3
        have h7 : x - 4 = (2 : ℝ) ^ (3 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith) ] at h6
          · nlinarith
          all_goals linarith
        have h8 : x = 12 := by
          norm_num at h7 ⊢
          linarith
        right
        right
        right
        exact h8
      · -- Real.logb 2 (x - 4) = -3
        have h7 : x - 4 = (2 : ℝ) ^ (-3 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith) ] at h6
          · nlinarith
          all_goals linarith
        have h8 : x = 33 / 8 := by
          norm_num at h7 ⊢
          nlinarith
        right
        left
        exact h8
    · -- Case where $\log_2(x-4)^2 = 4$
      have h5 : Real.logb 2 (x - 4) ^ 2 = 4 := by linarith
      have h6 : Real.logb 2 (x - 4) = 2 ∨ Real.logb 2 (x - 4) = -2 := by
        have h7 : Real.logb 2 (x - 4) ^ 2 - 4 = 0 := by linarith
        have h8 : Real.logb 2 (x - 4) ^ 2 - 4 = (Real.logb 2 (x - 4) - 2) * (Real.logb 2 (x - 4) + 2) := by ring
        rw [h8] at h7
        cases' (mul_eq_zero.1 h7) with h9 h10
        · -- Real.logb 2 (x - 4) - 2 = 0
          left
          linarith
        · -- Real.logb 2 (x - 4) + 2 = 0
          right
          linarith
      cases' h6 with h6 h6
      · -- Real.logb 2 (x - 4) = 2
        have h7 : x - 4 = (2 : ℝ) ^ (2 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith) ] at h6
          · nlinarith
          all_goals linarith
        have h8 : x = 8 := by
          norm_num at h7 ⊢
          linarith
        right
        right
        left
        exact h8
      · -- Real.logb 2 (x - 4) = -2
        have h7 : x - 4 = (2 : ℝ) ^ (-2 : ℝ) := by
          rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith) ] at h6
          · nlinarith
          all_goals linarith
        have h8 : x = 17 / 4 := by
          norm_num at h7 ⊢
          nlinarith
        left
        exact h8
  · -- Backward direction: proving the solutions satisfy the equation
    rintro (h | h | h | h)
    · -- x = 17/4
      rw [h]
      have h1 : Real.logb 2 (17 / 4 - 4) = -2 := by
        rw [show (17 / 4 - 4 : ℝ) = (1 / 4 : ℝ) by norm_num]
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num) ]
        · norm_num
        all_goals norm_num
      rw [h1]
      norm_num
    · -- x = 33/8
      rw [h]
      have h1 : Real.logb 2 (33 / 8 - 4) = -3 := by
        rw [show (33 / 8 - 4 : ℝ) = (1 / 8 : ℝ) by norm_num]
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num) ]
        · norm_num
        all_goals norm_num
      rw [h1]
      norm_num
    · -- x = 8
      rw [h]
      have h1 : Real.logb 2 (8 - 4) = 2 := by
        rw [show (8 - 4 : ℝ) = (4 : ℝ) by norm_num]
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num) ]
        · norm_num
        all_goals norm_num
      rw [h1]
      norm_num
    · -- x = 12
      rw [h]
      have h1 : Real.logb 2 (12 - 4) = 3 := by
        rw [show (12 - 4 : ℝ) = (8 : ℝ) by norm_num]
        rw [Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by norm_num) ]
        · norm_num
        all_goals norm_num
      rw [h1]
      norm_num