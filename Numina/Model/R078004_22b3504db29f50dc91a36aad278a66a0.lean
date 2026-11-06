import Mathlib

theorem algebra_302239 (x : ℝ) :
    Matrix.det (fun i j : Fin 3 => if i = 0 ∧ j = 0 then x + 1 else if i = 0 ∧ j = 1 then 2 * x else if i = 0 ∧ j = 2 then 1 else if i = 1 ∧ j = 0 then x else if i = 1 ∧ j = 1 then 3 * x - 2 else if i = 1 ∧ j = 2 then 2 * x else if i = 2 ∧ j = 0 then 1 else if i = 2 ∧ j = 1 then 1 else x) = 0 ↔
    x = 1 ∨ x = -2 + Real.sqrt 6 ∨ x = -2 - Real.sqrt 6 := by
  simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul]
  constructor
  · -- Forward implication: determinant equals zero → x is one of the three roots
    intro h
    have h1 : x^3 + 3 * x^2 - 6 * x + 2 = 0 := by 
      nlinarith 
    have h2 : (x - 1) * (x^2 + 4 * x - 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h2) with h3 h4
    · 
      left
      linarith 
    · 
      have h5 : x^2 + 4 * x - 2 = 0 := by 
        linarith 
      have h6 : (x - (-2 + Real.sqrt 6)) * (x - (-2 - Real.sqrt 6)) = 0 := by 
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
      cases' (mul_eq_zero.mp h6) with h7 h8
      · 
        right 
        left 
        linarith 
      · 
        right 
        right 
        linarith 
  · -- Backward implication: x is one of the three roots → determinant equals zero
    rintro (h | h | h)
    · 
      rw [h]
      norm_num 
    · 
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]
    · 
      rw [h]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 6 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)]