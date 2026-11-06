import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_186972 (f : ℝ → ℝ) (hf : f = λ x => x^3 - 3*x^2 + 5)
  (I : Set ℝ) (hI : I = Icc (-1) 1) :
  IsGreatest (image f I) 5 ∧ IsLeast (image f I) 1 := by
  constructor
  · -- Show 5 is greatest in image
    constructor
    · -- First show 5 is achievable, by finding an input
      use 0
      constructor
      · -- Show 0 is in the interval
        rw [hI]
        exact ⟨by norm_num, by norm_num⟩
      · -- Show f(0) = 5
        simp [hf]
        all_goals norm_num
    · -- Now show that 5 is indeed an upper bound
      intro y hy
      rw [hI] at hy
      rcases hy with ⟨x, ⟨hx1, hx2⟩, hfx⟩
      simp [hf] at hfx ⊢
      -- We need to show that y ≤ 5.
      -- That is, x^3 - 3x^2 + 5 ≤ 5
      -- Simplify to x^3 - 3x^2 ≤ 0
      -- Factor as x^2(x-3) ≤ 0
      -- Since x ∈ [-1, 1], x - 3 ≤ -2 (negative) and x^2 ≥ 0 (positive)
      -- Therefore, the product is non-positive
      nlinarith [sq_nonneg (x - 0), sq_nonneg (x - 2), sq_nonneg (x - 1), sq_nonneg (x + 1)]
  · -- Show 1 is least in image
    constructor
    · -- First show 1 is achievable, by finding an input
      use -1
      constructor
      · -- Show -1 is in the interval
        rw [hI]
        exact ⟨by norm_num, by norm_num⟩
      · -- Show f(-1) = 1
        simp [hf]
        all_goals norm_num
    · -- Now show that 1 is indeed a lower bound
      intro y hy
      rw [hI] at hy
      rcases hy with ⟨x, ⟨hx1, hx2⟩, hfx⟩
      simp [hf] at hfx ⊢
      -- We need to show that y ≥ 1
      -- That is, x^3 - 3x^2 + 5 ≥ 1
      -- Simplify to x^3 - 3x^2 ≥ -4
      -- x^3 - 3x^2 + 4 ≥ 0
      nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x - 0)]