import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_162740 (f : ℝ → ℝ) (hf : f = λ x => 2 * x ^ 3 - 6 * x + 5)
  (I : Set ℝ) (hI : I = Icc (-5 / 2) (3 / 2)) :
  IsGreatest (image f I) (9) ∧ IsLeast (image f I) (-11 - 1 / 4) := by

  constructor
  · -- Show that 9 is greatest in the image of f over I
    constructor
    · -- Show that 9 is in the image
      rw [hI]
      use -1
      constructor
      · norm_num
      · norm_num [hf]
    · -- Show that 9 is an upper bound
      intro y hy
      rw [hI] at hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      have h1 : -5 / 2 ≤ x := by
        linarith [hx.1, hx.2]
      have h2 : x ≤ 3 / 2 := by
        linarith [hx.1, hx.2]
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x - 3 / 2), sq_nonneg (x + 5 / 2),
                sq_nonneg (x * x - 1), sq_nonneg (x * x + 0.25)]
    
  · -- Now prove that -11 - 1/4 is the least
    constructor
    · -- Show that -11 - 1/4 is in the image
      rw [hI]
      use -5 / 2
      constructor
      · norm_num
      · norm_num [hf]
    · -- Show that -11 - 1/4 is a lower bound
      intro y hy
      rw [hI] at hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hf] at hfx
      simp at hfx
      have h1 : -5 / 2 ≤ x := by
        linarith [hx.1, hx.2]
      have h2 : x ≤ 3 / 2 := by
        linarith [hx.1, hx.2]
      nlinarith [sq_nonneg (x + 5 / 2), sq_nonneg (x - 3 / 2), sq_nonneg (x + 1), sq_nonneg (x - 1),
                sq_nonneg (x * x + 1 / 4), sq_nonneg (x * x - 1)]