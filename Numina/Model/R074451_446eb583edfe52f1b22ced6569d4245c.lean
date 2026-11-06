import Mathlib

open Real Set
open scoped Real

theorem algebra_71745 {x y : ℝ} (hy : 0 ≤ y ∧ y ≤ π/2)
  (h1 : x + sin y = 2008) (h2 : x + 2008 * cos y = 2007) :
  x + y = 2007 + π/2 := by 
  have h3 : sin y - 2008 * cos y = 1 := by
    linarith

  have h4 : sin y ≤ 1 := by 
    apply sin_le_one

  have h5 : 0 ≤ sin y := by
    apply sin_nonneg_of_nonneg_of_le_pi
    linarith [hy.left, hy.right, Real.pi_pos]
    linarith [hy.left, hy.right, Real.pi_pos]

  have h6 : 0 ≤ cos y := by 
    apply cos_nonneg_of_mem_Icc
    constructor
    linarith [hy.left, hy.right, Real.pi_pos]
    linarith [hy.left, hy.right, Real.pi_pos]

  have h7 : sin y = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq y, h3, sq_nonneg (sin y - 1), sq_nonneg (cos y)]

  have h8 : cos y = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq y, h7]

  have h9 : y = π / 2 := by
    have h5 : sin y = 1 := h7
    have h6 : cos y = 0 := h8
    have h11 : 0 ≤ y := hy.left
    have h12 : y ≤ π / 2 := hy.right
    have h13 : y = π / 2 := by 
      by_cases h : y < π / 2 
      · -- If y < π/2, then sin y < 1
        have h6 : sin y < 1 := by
          have h7 : sin (π / 2) = 1 := Real.sin_pi_div_two
          have h8 : sin y < sin (π / 2) := by 
            apply sin_lt_sin_of_lt_of_le_pi_div_two 
            all_goals linarith [h, Real.pi_pos]
          linarith [h7, h8]
        linarith [h5, h6]
      · -- Hence y must be equal to π/2 
        have : y ≥ π / 2 := by linarith 
        linarith
    exact h13

  have hx : x = 2007 := by
    linarith [h1, h7]

  linarith [hx, h9]