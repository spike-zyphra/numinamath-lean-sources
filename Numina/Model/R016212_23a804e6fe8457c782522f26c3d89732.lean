import Mathlib

theorem algebra_516 (x : ℝ) (hx : -4 ≤ x ∧ x ≤ 8) :
    IsLeast {y | ∃ x : ℝ, -4 ≤ x ∧ x ≤ 8 ∧ y = abs (abs (abs (x - 2) - 1) - 2) - 3} (-3) ∧
    IsGreatest {y | ∃ x : ℝ, -4 ≤ x ∧ x ≤ 8 ∧ y = abs (abs (abs (x - 2) - 1) - 2) - 3} 0 := by
  constructor
  · -- We need to prove that -3 is the least element in the set.
    constructor
    · -- Show that -3 is in the set.
      use 5
      norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos]
    · -- Show that for all y in the set, -3 ≤ y.
      intro y
      rintro ⟨x, hx1, hx2, h_eq⟩
      have h1 : -3 ≤ y := by
        rw [h_eq]
        have h2 : 0 ≤ abs (abs (abs (x - 2) - 1) - 2) := abs_nonneg (abs (abs (x - 2) - 1) - 2)
        linarith
      linarith
  · -- We need to prove that 0 is the greatest element in the set.
    constructor
    · -- Show that 0 is in the set.
      use 8
      norm_num [abs_of_pos, abs_of_nonneg, abs_of_nonpos]
    · -- Show that for all y in the set, y ≤ 0.
      intro y
      rintro ⟨x, hx1, hx2, h_eq⟩
      have h2 : y ≤ (0 : ℝ) := by
        rw [h_eq]
        have h3 : -4 ≤ x := hx1
        have h4 : x ≤ 8 := hx2
        have h5 : 0 ≤ abs (x - 2) := abs_nonneg (x - 2)
        have h6 : abs (x - 2) ≤ 6 := by
          have h7 : -4 ≤ x := by linarith
          have h8 : x ≤ 8 := by linarith
          have h9 : x - 2 ≥ -6 := by linarith
          have h10 : x - 2 ≤ 6 := by linarith
          have h11 : abs (x - 2) ≤ 6 := by
            apply abs_le.mpr
            constructor <;> linarith
          linarith
        have h7 : -1 ≤ abs (x - 2) - 1 := by
          have h7 : abs (x - 2) ≥ 0 := by apply abs_nonneg
          linarith
        have h8 : abs (x - 2) - 1 ≤ 5 := by
          have h6 : abs (x - 2) ≤ 6 := h6
          linarith
        have h9 : abs (abs (x - 2) - 1) ≤ 5 := by
          apply abs_le.mpr
          constructor
          · -- Show that -5 ≤ abs (x - 2) - 1
            have h7 : abs (x - 2) - 1 ≥ -1 := by
              have h7 : abs (x - 2) ≥ 0 := by apply abs_nonneg
              linarith
            linarith
          · -- Show that abs (x - 2) - 1 ≤ 5
            have h8 : abs (x - 2) - 1 ≤ 5 := by
              have h6 : abs (x - 2) ≤ 6 := h6
              linarith
            linarith
        have h10 : abs (abs (x - 2) - 1) - 2 ≥ -2 := by
          have h9 : abs (abs (x - 2) - 1) ≤ 5 := h9
          have h11 : abs (abs (x - 2) - 1) ≥ 0 := by apply abs_nonneg
          linarith
        have h11 : abs (abs (x - 2) - 1) - 2 ≤ 3 := by
          have h9 : abs (abs (x - 2) - 1) ≤ 5 := h9
          linarith
        have h13 : abs (abs (abs (x - 2) - 1) - 2) ≤ 3 := by
          apply abs_le.mpr
          constructor
          · -- Show that -3 ≤ (abs (abs (x - 2) - 1) - 2)
            linarith [h10]
          · -- Show that (abs (abs (x - 2) - 1) - 2) ≤ 3
            linarith [h11]
        have h12 : abs (abs (abs (x - 2) - 1) - 2) - 3 ≤ 0 := by
          linarith [h13]
        linarith
      linarith