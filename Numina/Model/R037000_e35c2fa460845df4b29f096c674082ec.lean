import Mathlib

theorem algebra_271229 (f : ℝ → ℝ) (hf : f = fun x => abs (x - 2) + abs (x - 3) - abs (x - 1)) :
    IsGreatest (Set.image f (Set.Icc 2 3)) 0 ∧ IsLeast (Set.image f (Set.Icc 2 3)) (-1) := by
  constructor
  · -- Show that 0 is the greatest element in the image of f over [2,3]
    constructor
    · -- Show that 0 is in the image
      use 2
      constructor
      · -- Show that 2 is in [2,3]
        exact ⟨by norm_num, by norm_num⟩
      · -- Calculate f(2) and show it equals 0
        rw [hf]
        norm_num [abs]
    · -- Show that for any y in the image, y ≤ 0
      intro y
      rintro ⟨x, hx, hfx⟩
      have h1 : 2 ≤ x ∧ x ≤ 3 := by
        exact hx
      rw [hf] at hfx
      have h2 : x ≥ 2 := h1.1
      have h3 : x ≤ 3 := h1.2
      have h4 : abs (x - 2) = x - 2 := by
        rw [abs_of_nonneg]
        linarith
      have h5 : abs (x - 3) = 3 - x := by
        rw [abs_of_nonpos]
        linarith
        all_goals linarith
      have h6 : abs (x - 1) = x - 1 := by
        rw [abs_of_nonneg]
        linarith
      simp [h4, h5, h6] at hfx
      linarith
  · -- Show that -1 is the least element in the image of f over [2,3]
    constructor
    · -- Show that -1 is in the image
      use 3
      constructor
      · -- Show that 3 is in [2,3]
        exact ⟨by norm_num, by norm_num⟩
      · -- Calculate f(3) and show it equals -1
        rw [hf]
        norm_num [abs]
    · -- Show that for any y in the image, -1 ≤ y
      intro y
      rintro ⟨x, hx, hfx⟩
      have h1 : 2 ≤ x ∧ x ≤ 3 := by
        exact hx
      rw [hf] at hfx
      have h2 : x ≥ 2 := h1.1
      have h3 : x ≤ 3 := h1.2
      have h4 : abs (x - 2) = x - 2 := by
        rw [abs_of_nonneg]
        linarith
      have h5 : abs (x - 3) = 3 - x := by
        rw [abs_of_nonpos]
        linarith
        all_goals linarith
      have h6 : abs (x - 1) = x - 1 := by
        rw [abs_of_nonneg]
        linarith
      simp [h4, h5, h6] at hfx
      linarith