import Mathlib


theorem algebra_22113 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * (4 - x) ^ 2 + b * (4 - x) + c = a * x ^ 2 + b * x + c)
    (h1 : a * 1 ^ 2 + b * 1 + c = 1) (h2 : a * 4 ^ 2 + b * 4 + c = -1)
    (x1 x2 : ℝ)
    (root1: x1 > x2)
    (root2: a * x1 ^ 2 + b * x1 + c = 0 ∧ a * x2 ^ 2 + b * x2 + c = 0)
    (n: ℝ)
    (root3: x1 = Real.sqrt n + 2) : n = 5 / 2 := by

  have h3 : b = -4 * a := by 
    specialize h 0
    linarith

  have h4 : c = -1 := by
    have eq1 := h1
    rw [show b = -4 * a by linarith [h3]] at h1
    nlinarith

  have h5 : a = -2/3 := by
    rw [show b = -4 * a by linarith [h3]] at h1
    rw [show c = -1 by linarith [h4]] at h1
    linarith

  have h6 : b = 8/3 := by
    rw [show a = -2/3 by linarith [h5]] at h3
    linarith

  have h7 : a * x1 ^ 2 + b * x1 + c = 0 := root2.1
  rw [show a = -2/3 by linarith [h5]] at h7
  rw [show b = 8/3 by linarith [h6]] at h7
  rw [show c = -1 by linarith [h4]] at h7
  have h8 : 2 * x1 ^ 2 - 8 * x1 + 3 = 0 := by nlinarith

  have h9 : (x1 - (2 + Real.sqrt 10 / 2)) * (x1 - (2 - Real.sqrt 10 / 2)) = 0 := by 
    nlinarith [Real.sqrt_pos.mpr (show 0 < (10 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]

  cases' (mul_eq_zero.mp h9) with h10 h11
  ·
    have h12 : x1 = 2 + Real.sqrt 10 / 2 := by linarith
    rw [h12] at root3
    have h14 : Real.sqrt n = Real.sqrt 10 / 2 := by
      nlinarith
    have h14' : n = 5 / 2 := by 
      have h14'' : (Real.sqrt n) ^ 2 = (Real.sqrt 10 / 2) ^ 2 := by
        rw [h14]
      have h14''' : (Real.sqrt n) ^ 2 = n := by 
        rw [Real.sq_sqrt (show 0 ≤ n by 
          by_contra h 
          push_neg at h 
          have h13 : Real.sqrt n = 0 := by
            rw [Real.sqrt_eq_zero']
            all_goals linarith
          nlinarith
        )]
      have h14_04 : (Real.sqrt 10 / 2) ^ 2 = (10 / 4) := by 
        calc 
          (Real.sqrt 10 / 2) ^ 2 = (Real.sqrt 10) ^ 2 / 4 := by ring
          _ = 10 / 4 := by
            rw [Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
            <;> nlinarith
      nlinarith
    linarith
  ·
    have h12 : x1 = 2 - Real.sqrt 10 / 2 := by linarith
    rw [h12] at root3
    have h14 : Real.sqrt n = - (Real.sqrt 10 / 2) := by
      nlinarith
    have h14' : Real.sqrt n ≥ 0 := Real.sqrt_nonneg n
    nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]