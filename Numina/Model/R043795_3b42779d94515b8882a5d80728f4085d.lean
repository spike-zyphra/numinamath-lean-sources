import Mathlib

open Real Set

theorem inequalities_131719 (x : ℝ) :
    abs (abs (abs (2 - x) - x) - 8) ≤ 2008 ↔ x ≥ -1007 := by
  constructor
  · -- Assume abs (abs (abs (2 - x) - x) - 8) ≤ 2008, prove x ≥ -1007
    intro h
    have h1 : -2008 ≤ abs (abs (2 - x) - x) - 8 := by
      linarith [abs_le.mp h]
    have h2 : abs (abs (2 - x) - x) - 8 ≤ 2008 := by
      linarith [abs_le.mp h]
    have h3 : -2000 ≤ abs (abs (2 - x) - x) := by 
      linarith
    have h4 : abs (abs (2 - x) - x) ≤ 2016 := by 
      linarith
    have h7 : -2016 ≤ abs (2 - x) - x := by
      cases abs_le.mp h4 with
      | intro h8 h9 =>
        linarith
    have h8 : abs (2 - x) - x ≤ 2016 := by
      cases abs_le.mp h4 with
      | intro h8 h9 =>
        linarith
    by_cases h9 : 2 - x ≥ 0
    · -- Case where 2 - x ≥ 0, so x ≤ 2.
      have h10 : abs (2 - x) = 2 - x := by
        rw [abs_of_nonneg h9]
      have h11 : abs (2 - x) - x = 2 - 2 * x := by
        rw [h10]
        all_goals nlinarith
      have h12 : -2016 ≤ 2 - 2 * x := by
        linarith [h7, h11]
      have h13 : 2 - 2 * x ≤ 2016 := by
        linarith [h8, h11]
      nlinarith
    · -- Case where 2 - x < 0, so x > 2.
      have h10 : abs (2 - x) = x - 2 := by
        rw [abs_of_neg (show (2 - x : ℝ) < 0 by linarith)]
        all_goals
        linarith
      have h11 : abs (2 - x) - x = -2 := by
        rw [h10]
        all_goals nlinarith
      have h12 : -2016 ≤ -2 := by
        linarith [h7, h11]
      have h13 : -2 ≤ 2016 := by
        linarith [h8, h11]
      nlinarith
  · -- Assume x ≥ -1007, prove abs (abs (abs (2 - x) - x) - 8) ≤ 2008
    intro h
    have h3 : -2016 ≤ abs (2 - x) - x := by
      by_cases h5 : 2 - x ≥ 0
      · -- 2 - x ≥ 0, so x ≤ 2
        have h6 : abs (2 - x) = 2 - x := abs_of_nonneg h5
        rw [h6]
        have h5' : x ≥ -1007 := h
        nlinarith
      · -- 2 - x < 0, so x > 2
        have h6 : abs (2 - x) = x - 2 := by
          rw [abs_of_neg (by linarith)]
          all_goals linarith
        rw [h6]
        have h5' : x ≥ -1007 := h
        nlinarith
    have h4 : abs (2 - x) - x ≤ 2016 := by
      by_cases h5 : 2 - x ≥ 0
      · -- 2 - x ≥ 0, so x ≤ 2
        have h6 : abs (2 - x) = 2 - x := abs_of_nonneg h5
        rw [h6]
        have h5' : x ≥ -1007 := h
        nlinarith
      · -- 2 - x < 0, so x > 2
        have h6 : abs (2 - x) = x - 2 := by
          rw [abs_of_neg (by linarith)]
          all_goals linarith
        rw [h6]
        have h5' : x ≥ -1007 := h
        nlinarith
    have h5 : abs (abs (2 - x) - x) ≤ 2016 := by
      apply abs_le.mpr
      constructor
      · linarith
      · linarith
    have h6 : abs (2 - x) - x ≥ -2 := by
      by_cases h5 : 2 - x ≥ 0
      · -- 2 - x ≥ 0, so x ≤ 2 
        have h6 : abs (2 - x) = 2 - x := abs_of_nonneg h5
        rw [h6]
        nlinarith
      · -- 2 - x < 0, so x > 2 
        have h6 : abs (2 - x) = x - 2 := by
          rw [abs_of_neg (by linarith)]
          all_goals linarith
        rw [h6]
        nlinarith
    have h7 : -2008 ≤ abs (abs (2 - x) - x) - 8 := by
      have h6' : abs (abs (2 - x) - x) ≥ 0 := by
        apply abs_nonneg
      nlinarith [abs_nonneg (abs (2 - x) - x), h6, abs_le.mp h5]
    have h8 : abs (abs (2 - x) - x) - 8 ≤ 2008 := by
      have h6' : abs (abs (2 - x) - x) ≥ 0 := by
        apply abs_nonneg
      nlinarith [abs_nonneg (abs (2 - x) - x), h6, abs_le.mp h5]
    apply abs_le.mpr
    constructor <;> linarith