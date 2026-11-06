import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_178754 {f : ℝ → ℝ} (hf : f = λ x => x^3 - 3 * x^2 + 1) :
    IsGreatest (image f (Set.Ioo (-1) 1)) 1 ∧ ∃ x ∈ Set.Ioo (-1) 1, f x = 1 := by
  constructor
  · -- Show that 1 is the greatest in the image of f over (-1, 1).
    constructor
    · -- First show that 1 is in the image of f over (-1, 1).
      use 0
      constructor
      · -- Show that 0 ∈ (-1, 1).
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that f(0) = 1.
        rw [hf]
        norm_num
    · -- Now show that 1 is the greatest value in the image.
      intro y
      rintro ⟨x, hx, hfx⟩
      rw [hf] at hfx
      have h1 : x ∈ Set.Ioo (-1 : ℝ) 1 := by
        simpa using hx
      rcases h1 with ⟨h11, h12⟩
      simp at hfx
      have h2 : x ^ 3 - 3 * x ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (x : ℝ), sq_nonneg ((x - 0) : ℝ), sq_nonneg (x - 2 : ℝ), sq_nonneg ((x - 3 : ℝ)), sq_nonneg ((x - 0)), sq_nonneg ((x + 1)), sq_nonneg ((1 - x)), mul_pos (show (0 : ℝ) < x + 1 by linarith) (show (0 : ℝ) < 1 - x by linarith)]
      nlinarith
  · -- Show that there exists an x ∈ (-1, 1) such that f(x) = 1.
    use 0
    constructor
    · -- Show that 0 ∈ (-1, 1).
      exact ⟨by norm_num, by norm_num⟩
    · -- Show that f(0) = 1.
      rw [hf]
      norm_num