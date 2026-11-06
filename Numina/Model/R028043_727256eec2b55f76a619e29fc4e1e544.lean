import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_187511 (f : ℝ → ℝ) (hf : f = λ x => 3 * x ^ 4 + 4 * x ^ 3 + 34)
  (I : Set ℝ) (hI : I = Icc (-2) 1) :
  IsGreatest (image f I) 50 ∧ IsLeast (image f I) 33 := by
  constructor
  · -- Show that 50 is greatest in image.
    constructor
    · -- Show that 50 in the image.
      rw [hI]
      use -2
      constructor
      · -- Verify that -2 is in the interval.
        exact ⟨by norm_num, by norm_num⟩
      · -- Verify that $f(-2) = 50 $.
        rw [hf]
        norm_num
    · -- Show that for any element in image, it's ≤ 50.
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hI] at hx
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx1, hx2⟩
      nlinarith [sq_nonneg (x + 2), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - 1),
        sq_nonneg (x ^ 2 + 1), sq_nonneg (x * (x + 1)), sq_nonneg ((x + 1)), sq_nonneg ((x - 1)), 
        sq_nonneg ((x + 2)), mul_nonneg (show (0 : ℝ) ≤ x + 2 by nlinarith) 
          (show (0 : ℝ) ≤ 1 - x by nlinarith)]
  · -- Show that 33 is least in image.
    constructor
    · -- Show that 33 in the image.
      rw [hI]
      use -1
      constructor
      · -- Verify that -1 is in the interval.
        exact ⟨by norm_num, by norm_num⟩
      · -- Verify that $f(-1) = 33 $.
        rw [hf]
        norm_num
    · -- Show that any element in image is ≥ 33.
      intro y hy
      rcases hy with ⟨x, hx, hfx⟩
      rw [hI] at hx
      rw [hf] at hfx
      simp at hfx
      rcases hx with ⟨hx1, hx2⟩
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x ^ 2 - 1),
        sq_nonneg (x ^ 2 + 1), sq_nonneg (x * (x + 1)), sq_nonneg ((x + 1)), sq_nonneg ((x - 1)), 
        sq_nonneg ((x + 2)), mul_nonneg (show (0 : ℝ) ≤ x + 2 by nlinarith) 
          (show (0 : ℝ) ≤ 1 - x by nlinarith)]