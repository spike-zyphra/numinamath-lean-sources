import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_221829:
    IsGreatest {s : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ s = min (min x (y + 1/x)) (1/y)} (Real.sqrt 2) := by
  constructor
  · -- Show that √2 is in the set
    use Real.sqrt 2, (1 / Real.sqrt 2)
    constructor
    · -- Show that x > 0
      positivity
    constructor
    · -- Show that y > 0
      positivity
    · -- Show that s = min (min x (y + 1 / x)) (1 / y)
      have h1 : Real.sqrt 2 > 0 := by positivity
      have h2 : (1 / Real.sqrt 2 : ℝ) > 0 := by positivity
      have h3 : (1 / Real.sqrt 2 : ℝ) + 1 / (Real.sqrt 2) = Real.sqrt 2 := by
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > (0 : ℝ) by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ (0 : ℝ) by norm_num)]
      have h4 : (1 / ( (1 / Real.sqrt 2) : ℝ )) = Real.sqrt 2 := by 
        field_simp
      rw [show min (min (Real.sqrt 2) ((1 / Real.sqrt 2 + 1 / Real.sqrt 2))) (1 / (1 / Real.sqrt 2)) = Real.sqrt 2 by 
        rw [show (1 / Real.sqrt 2 + 1 / Real.sqrt 2 : ℝ) = Real.sqrt 2 by linarith [h3]]
        rw [show (1 / ( (1 / Real.sqrt 2) : ℝ )) = Real.sqrt 2 by linarith [h4]]
        norm_num
      ]
  · -- Show that √2 is the greatest element in the set
    intro s hs
    rcases hs with ⟨x, y, hx, hy, hs⟩
    by_contra h
    push_neg at h
    have h1 : min (min x (y + 1 / x)) (1 / y) > Real.sqrt 2 := by
      linarith
    have h2 : x > Real.sqrt 2 := by
      by_contra h'
      push_neg at h'
      have h3 : min (min x (y + 1 / x)) (1 / y) ≤ x := by
        have h4 : min (min x (y + 1 / x)) (1 / y) ≤ min x (y + 1 / x) := by 
          apply min_le_left
        have h5 : min x (y + 1 / x) ≤ x := by 
          apply min_le_left
        linarith
      nlinarith
    have h3 : (1 / y : ℝ) > Real.sqrt 2 := by 
      have h4 : min (min x (y + 1 / x)) (1 / y) ≤ (1 / y : ℝ) := by 
        apply min_le_right
      nlinarith
    have h4 : y < 1 / Real.sqrt 2 := by 
      by_contra h'
      push_neg at h'
      have h5 : (1 / y : ℝ) ≤ Real.sqrt 2 := by
        have h6 : y ≥ 1 / Real.sqrt 2 := by linarith
        have h7 : (1 / y : ℝ) ≤ (1 / (1 / Real.sqrt 2) : ℝ) := by 
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          linarith
        have h8 : (1 / ( (1 / Real.sqrt 2) : ℝ ) ) = Real.sqrt 2 := by 
          field_simp
        nlinarith [h7, h8]
      linarith
    have h5 : y + 1 / x > Real.sqrt 2 := by 
      have h6 : min (min x (y + 1 / x)) (1 / y) ≤ y + 1 / x := by 
        have h7 : min (min x (y + 1 / x)) (1 / y) ≤ min x (y + 1 / x) := by 
          apply min_le_left
        have h8 : min x (y + 1 / x) ≤ y + 1 / x := by 
          apply min_le_right
        linarith
      nlinarith
    have h6 : y + 1 / x < Real.sqrt 2 := by 
      have h7 : x > Real.sqrt 2 := h2
      have h8 : 1 / x < 1 / Real.sqrt 2 := by 
        apply (div_lt_div_iff (by positivity) (by positivity)).mpr
        linarith
      have h9 : y < 1 / Real.sqrt 2 := h4
      have h10 : y + 1 / x < (1 / Real.sqrt 2 : ℝ) + (1 / Real.sqrt 2 : ℝ) := by 
        linarith [h8, h9]
      have h11 : (1 / Real.sqrt 2 + 1 / Real.sqrt 2 : ℝ) = Real.sqrt 2 := by 
        field_simp
        <;> nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]
      linarith
    linarith