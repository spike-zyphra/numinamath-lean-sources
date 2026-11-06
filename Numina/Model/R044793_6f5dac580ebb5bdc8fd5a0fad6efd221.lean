import Mathlib

open Polynomial

theorem algebra_10632 {f : ℝ → ℝ} (hf : f = fun x => x^2 - 3 * x + 2) :
    Set.ncard {x | f (f x) = 0} = 4 := by

  have h1 : {x : ℝ | f (f x) = 0} = { (3 + Real.sqrt 5) / 2, (3 - Real.sqrt 5) / 2, (0 : ℝ), (3 : ℝ) } := by
    ext x
    simp [hf]
    constructor
    · -- Assume f(f(x)) = 0, prove x in the set
      intro h
      have h2 : (x^2 - 3 * x + 2)^2 - 3 * (x^2 - 3 * x + 2) + 2 = 0 := by
        nlinarith
      have h3 : (x^2 - 3 * x + 1) * (x^2 - 3 * x) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h3) with h4 h5
      · -- Case $x^2 - 3 * x + 1 = 0$
        have h6 : x^2 - 3 * x + 1 = 0 := h4
        have h7 : (x - (3 + Real.sqrt 5) / 2) * (x - (3 - Real.sqrt 5) / 2) = 0 := by
          nlinarith [Real.sqrt_pos.mpr (by norm_num : (5 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), sq_nonneg (x - 3 / 2), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
        cases' (mul_eq_zero.1 h7) with h8 h9
        · -- Case $x - (3 + Real.sqrt 5) / 2 = 0$
          have hx1 : x = (3 + Real.sqrt 5) / 2 := by linarith
          simp [hx1]
        · -- Case $x - (3 - Real.sqrt 5) / 2 = 0$
          have hx2 : x = (3 - Real.sqrt 5) / 2 := by linarith
          simp [hx2]
      · -- Case $x^2 - 3 * x = 0$
        have h8 : x^2 - 3 * x = 0 := h5
        have h9 : x * (x - 3) = 0 := by
          linarith
        cases' (mul_eq_zero.1 h9) with h10 h11
        · -- Case $x = 0$
          have hx0 : x = (0 : ℝ) := by linarith
          simp [hx0]
        · -- Case $x - 3 = 0$
          have hx3 : x = (3 : ℝ) := by linarith
          simp [hx3]
    · -- Assume x in the set, prove f(f(x)) = 0
      rintro (h | h | h | h)
      · -- Case x = (3 + Real.sqrt 5) / 2
        rw [h]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt (5 : ℝ) - 1), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
      · -- Case x = (3 - Real.sqrt 5) / 2
        rw [h]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), sq_nonneg (Real.sqrt (5 : ℝ) - 1), Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num)]
      · -- Case x = 0
        rw [h]
        norm_num
      · -- Case x = 3
        rw [h]
        norm_num

  rw [h1]
  have h2 : Real.sqrt 5 > 0 := by
    positivity
  have h3 : (3 + Real.sqrt 5) / 2 ≠ (3 - Real.sqrt 5) / 2 := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h4 : (3 + Real.sqrt 5) / 2 ≠ (0 : ℝ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h5 : (3 + Real.sqrt 5) / 2 ≠ (3 : ℝ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h6 : (3 - Real.sqrt 5) / 2 ≠ (0 : ℝ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h7 : (3 - Real.sqrt 5) / 2 ≠ (3 : ℝ) := by
    intro h
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h8 : (0 : ℝ) ≠ (3 : ℝ) := by norm_num
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton, h3, h4, h5, h6, h7, h8]
  all_goals linarith