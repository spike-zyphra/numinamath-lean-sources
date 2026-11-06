import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_246049 :
  IsGreatest {s | ∃ x y : ℝ, x > 0 ∧ y > 0 ∧ s = min (min x (y + 1 / x)) (1 / y)} (Real.sqrt 2) := by
  constructor
  · -- Show that sqrt(2) is indeed in the set, using x = sqrt(2) and y = sqrt(2)/2
    use Real.sqrt 2, Real.sqrt 2 / 2
    constructor
    · -- Show that sqrt(2) > 0
      positivity
    constructor
    · -- Show that sqrt(2)/2 > 0
      positivity
    · -- Verify that sqrt(2) = min (min x (y + 1 / x)) (1 / y)
      have h1 : Real.sqrt 2 > 0 := by positivity
      have h2 : Real.sqrt 2 / 2 > 0 := by positivity
      have h3 : Real.sqrt 2 / 2 + 1 / Real.sqrt 2 = Real.sqrt 2 := by
        have h4 : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
          field_simp [Real.sqrt_ne_zero']
          <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        rw [h4]
        all_goals ring
      have h4 : 1 / (Real.sqrt 2 / 2) = Real.sqrt 2 := by
        field_simp [Real.sqrt_ne_zero']
        <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
      rw [h3, h4]
      all_goals norm_num [h1]
      all_goals linarith
  · -- Show that sqrt(2) is the greatest such value
    rintro s ⟨x, y, hx, hy, hs⟩
    by_contra h
    push_neg at h
    have h1 : s = min (min x (y + 1 / x)) (1 / y) := by linarith [hs]
    rw [h1] at h

    have h2 : x > Real.sqrt 2 := by
      by_contra h7
      push_neg at h7
      have h8 : x ≤ Real.sqrt 2 := by linarith
      have h9 : min (min x (y + 1 / x)) (1 / y) ≤ x := by
        simp [min_le_iff]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, h8]

    have h5 : y + 1 / x > Real.sqrt 2 := by
      by_contra h7
      push_neg at h7
      have h8 : y + 1 / x ≤ Real.sqrt 2 := by linarith
      have h9 : min (min x (y + 1 / x)) (1 / y) ≤ y + 1 / x := by
        simp [min_le_iff]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, h8]

    have h6 : 1 / y > Real.sqrt 2 := by 
      by_contra h7
      push_neg at h7
      have h8 : 1 / y ≤ Real.sqrt 2 := by linarith
      have h9 : min (min x (y + 1 / x)) (1 / y) ≤ 1 / y := by
        simp [min_le_iff]
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, h8]

    have hy1 : y < 1 / Real.sqrt 2 := by
      by_contra h8
      push_neg at h8
      have h9 : 1 / y ≤ Real.sqrt 2 := by
        have h10 : y ≥ 1 / Real.sqrt 2 := by linarith
        have h11 : 1 / y ≤ 1 / (1 / Real.sqrt 2) := by
          apply one_div_le_one_div_of_le
          positivity
          linarith
        have h12 : 1 / (1 / Real.sqrt 2) = Real.sqrt 2 := by
          field_simp
        linarith [h11, h12]
      linarith

    have hx1 : 1 / x < 1 / Real.sqrt 2 := by
      have h7 : x > Real.sqrt 2 := h2
      have h8 : 1 / x < 1 / Real.sqrt 2 := by
        apply one_div_lt_one_div_of_lt
        all_goals nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
      linarith

    have h11 : y + 1 / x < Real.sqrt 2 := by
      have h12 : y < 1 / Real.sqrt 2 := by linarith [hy1]
      have h13 : 1 / x < 1 / Real.sqrt 2 := by linarith [hx1]
      nlinarith [show (1 / Real.sqrt 2 + 1 / Real.sqrt 2 : ℝ) = Real.sqrt 2 by
        have eq1 : (1 / Real.sqrt 2 + 1 / Real.sqrt 2 : ℝ) = 2 / Real.sqrt 2 := by 
          ring
        rw [eq1]
        field_simp
        <;> ring_nf <;> norm_num [Real.sq_sqrt]
      ]

    -- Combine h5 and h11 to get the contradiction
    linarith [h5, h11]