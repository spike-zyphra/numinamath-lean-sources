import Mathlib
open Polynomial

theorem algebra_5625 {P Q : ℝ[X]} (hP : P = X^3 - 3 * X - 2)
    (hQ : Q = X^3 - 5 * X^2 + 8 * X - 4) (r : ℝ) (hr : P.eval r = 0) (hr' : Q.eval r = 0) :
    IsGreatest { x | P.eval x = 0 } r ∧ IsLeast { x | Q.eval x = 0 } (r - 1) := by

  have h1 : r^3 - 3 * r - 2 = 0 := by 
    rw [hP] at hr 
    simp at hr 
    linarith

  have h2 : r^3 - 5 * r^2 + 8 * r - 4 = 0 := by 
    rw [hQ] at hr'
    simp at hr'
    linarith

  have h3 : 5 * r^2 - 11 * r + 2 = 0 := by
    nlinarith [sq_nonneg (r^2), sq_nonneg (r - 2), sq_nonneg (r - 1 / 5)]

  have h4 : (r - 2) * (5 * r - 1) = 0 := by 
    nlinarith

  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case r - 2 = 0, so r = 2 
    have hr_eq_2 : r = 2 := by linarith
    constructor 
    · -- Show r is greatest in {x | P.eval x = 0}
      constructor
      · -- Show r is in the set
        rw [hP]
        simp at *
        rw [hr_eq_2]
        norm_num
      · -- Show r is greatest
        intro x hx
        rw [hP] at hx
        simp at hx 
        have h51 : x^3 - 3 * x - 2 = 0 := by 
          linarith [hx]
        have h52 : (x - 2) * (x + 1)^2 = 0 := by nlinarith 
        cases' (mul_eq_zero.1 h52) with h53 h54
        · -- Case x - 2 = 0, so x = 2
          have hx_eq_2 : x = 2 := by linarith 
          linarith [hr_eq_2, hx_eq_2]
        · -- Case (x + 1)^2 = 0 
          have hx_eq_neg_1 : x = -1 := by 
            nlinarith 
          linarith [hr_eq_2, hx_eq_neg_1]
    · -- Show r - 1 is least in {x | Q.eval x = 0}
      constructor
      · -- Show r - 1 is in the set 
        rw [hQ]
        simp at *
        rw [hr_eq_2]
        norm_num 
      · -- Show r - 1 is least 
        intro x hx 
        rw [hQ] at hx 
        simp at hx 
        have h21 : x^3 - 5 * x^2 + 8 * x - 4 = 0 := by 
          linarith [hx]
        have h22 : (x - 1) * (x - 2)^2 = 0 := by nlinarith 
        cases' (mul_eq_zero.1 h22) with h23 h24 
        · -- Case x - 1 = 0, so x = 1 
          have hx_eq_1 : x = 1 := by linarith 
          linarith [hr_eq_2, hx_eq_1]
        · -- Case (x - 2)^2 = 0 
          have hx_eq_2 : x = 2 := by nlinarith 
          linarith [hr_eq_2, hx_eq_2]
  · -- Case 5 * r - 1 = 0 
    have hr_eq_1_5 : r = 1 / 5 := by 
      linarith 
    rw [hP] at hr 
    simp at hr
    rw [hr_eq_1_5] at hr 
    norm_num at hr 
    all_goals nlinarith