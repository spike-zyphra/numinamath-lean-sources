import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_277165 :
  IsGreatest {s : ℝ | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ s = min (min x (y + 1/x)) (1/y)} (Real.sqrt 2) := by
  constructor
  · -- Show that sqrt 2 is in the set
    use Real.sqrt 2, Real.sqrt 2 / 2
    constructor
    · positivity
    constructor
    · positivity
    · -- Show that with these values of x and y, s = sqrt 2
      have h1 : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
      have h2 : Real.sqrt 2 / 2 > 0 := by
        apply div_pos
        exact Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)
        norm_num
      have h3 : Real.sqrt 2 / 2 + 1 / (Real.sqrt 2) = Real.sqrt 2 := by
        field_simp [show Real.sqrt 2 ≠ 0 by positivity]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h4 : min (Real.sqrt 2) (Real.sqrt 2 / 2 + 1 / (Real.sqrt 2)) = Real.sqrt 2 := by
        rw [h3]
        apply min_eq_left
        all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      have h5 : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
        field_simp [show Real.sqrt 2 ≠ 0 by positivity]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      rw [show min (min (Real.sqrt 2) (Real.sqrt 2 / 2 + 1 / (Real.sqrt 2))) (1 / (Real.sqrt 2 / 2)) = Real.sqrt 2 by
        rw [h4, h5]
        apply min_eq_left
        all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      ]
  · -- Show that sqrt 2 is greatest in the set
    intro s hs
    rcases hs with ⟨x, y, hx, hy, h_eq⟩
    by_contra h
    push_neg at h
    have h1 : s ≥ Real.sqrt 2 := by linarith
    have h3 : s ≤ x := by
      have h4 : s ≤ min (min x (y + 1 / x)) (1 / y) := by 
        linarith [h_eq]
      have h4a : min (min x (y + 1 / x)) (1 / y) ≤ min x (y + 1 / x) := by
        apply min_le_left
      have h6 : min x (y + 1 / x) ≤ x := by 
        apply min_le_left
      linarith [h4, h4a, h6]
    have h4 : s ≤ 1 / y := by
      have h5 : s ≤ min (min x (y + 1 / x)) (1 / y) := by 
        linarith [h_eq]
      have h5a : min (min x (y + 1 / x)) (1 / y) ≤ 1 / y := by 
        apply min_le_right
      linarith [h5, h5a]
    have h5 : s ≤ y + 1 / x := by
      have h6 : s ≤ min (min x (y + 1 / x)) (1 / y) := by 
        linarith [h_eq]
      have h7 : min (min x (y + 1 / x)) (1 / y) ≤ min x (y + 1 / x) := by 
        apply min_le_left
      have h8 : min x (y + 1 / x) ≤ y + 1 / x := by 
        apply min_le_right
      linarith [h7, h8, h6]
    -- From s > sqrt 2 derive bounds
    have h8 : x > Real.sqrt 2 := by
      by_contra h
      push_neg at h
      nlinarith [h3, h, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    have h9 : (1 / y) > Real.sqrt 2 := by
      by_contra h
      push_neg at h
      nlinarith [h4, h, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    -- From 1/y > sqrt 2, we get y < 1/sqrt 2
    have h10 : y < (1 / Real.sqrt 2) := by
      by_contra h11
      push_neg at h11
      have h15 : (1 / y) ≤ Real.sqrt 2 := by 
        have h16 : y ≥ (1 / Real.sqrt 2) := by linarith [h11]
        have h17 : (1 / y) ≤ Real.sqrt 2 := by 
          apply (one_div_le (by positivity) (by positivity)).mpr
          linarith [h16, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
        linarith
      linarith [h9, h15, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
    -- Show that y + 1/x < Real.sqrt 2
    have h11 : y + 1 / x < Real.sqrt 2 := by
      have h14 : x > Real.sqrt 2 := h8
      have h15 : y < (1 / Real.sqrt 2) := h10
      have h16 : 1 / x < (1 / Real.sqrt 2) := by
        apply (one_div_lt (by positivity) (by positivity)).mpr
        linarith [h14, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num)]
      have h17 : y + 1 / x < (1 / Real.sqrt 2) + (1 / Real.sqrt 2) := by 
        linarith [h15, h16]
      have h18 : (1 / Real.sqrt 2) + (1 / Real.sqrt 2) = Real.sqrt 2 := by
        field_simp [show Real.sqrt 2 ≠ 0 by positivity]
        <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      linarith [h17, h18]
    -- Contradiction
    linarith [h11, h5, h]