import Mathlib

theorem algebra_297985 (f : ℝ → ℝ) (hf : f = fun x => x - abs (1 + x)) :
    IsGreatest (Set.image f (Set.Icc (-2) 2)) (-1) ∧ IsLeast (Set.image f (Set.Icc (-2) 2)) (-3) := by

  constructor
  · -- Show that -1 is the greatest element of the image
    constructor
    · -- Show that -1 is obtained by some input in the domain
      use (0)
      constructor
      · -- Show that 0 is within the domain
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(0) = -1
        rw [hf]
        norm_num
    · -- Show that -1 is an upper bound of the image
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx1, hx2⟩
      by_cases h : 1 + x ≥ 0
      · -- Case where 1 + x >= 0 (x >= -1)
        rw [abs_of_nonneg h] at hfx
        nlinarith
      · -- Case where 1 + x < 0 (x < -1)
        have h' : 1 + x < 0 := by linarith
        rw [abs_of_neg h'] at hfx
        nlinarith
  · -- Show that -3 is the least element of the image
    constructor
    · -- Show that -3 is obtained by some input in the domain
      use (-2)
      constructor
      · -- Show that -2 is within the domain
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(-2) = -3
        rw [hf]
        norm_num
    · -- Show that -3 is a lower bound of the image
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx1, hx2⟩
      by_cases h : 1 + x ≥ 0
      · -- Case where 1 + x >= 0 (x >= -1)
        rw [abs_of_nonneg h] at hfx
        nlinarith
      · -- Case where 1 + x < 0 (x < -1)
        have h' : 1 + x < 0 := by linarith
        rw [abs_of_neg h'] at hfx
        nlinarith