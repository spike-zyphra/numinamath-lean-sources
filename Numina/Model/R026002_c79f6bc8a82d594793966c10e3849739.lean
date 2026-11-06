import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_13765 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 0 → f x ≠ 0)
  (h1 : ∀ x, f (1 / x) = x * f x) (h2 : ∀ x y, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
  f (1 / x) + f (1 / y) = 1 + f (1 / (x + y))) :
  ∃! s, f 1 = s ∧ s = 2 := by

  -- First we need to compute f(-1)
  have h3 : f (-1) = 0 := by
    specialize h1 (-1)
    norm_num at h1
    linarith

  -- Next, compute f(-1/2)
  have h4 : f (-1 / 2) = -1 := by
    specialize h2 (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    norm_num [h3] at h2 ⊢
    linarith

  -- Then compute f(-2)
  have h5 : f (-2) = 1 / 2 := by
    specialize h1 (-2)
    norm_num [h4] at h1 ⊢
    linarith

  -- From x=1, y=1: f(1/1) + f(1/1) = 1 + f(1/(1+1)), so f(1) + f(1) = 1 + f(1/2)
  have h6 : f (1 / (2 : ℝ)) = 2 * f 1 - 1 := by
    specialize h2 1 1 (by norm_num) (by norm_num) (by norm_num)
    norm_num at h2 ⊢
    linarith

  -- From x=2, y=-1: f(1/2) + f(-1) = 1 + f(1/(2 + (-1))), so f(1/2) + 0 = 1 + f(1)
  have h7 : f (1 / (2 : ℝ)) = 1 + f 1 := by
    specialize h2 (2 : ℝ) (-1 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    norm_num [h3] at h2 ⊢
    linarith

  -- Now solve for f(1)
  have h8 : f 1 = 2 := by
    linarith

  -- Now need to complete the proof of existence and uniqueness of s such that f(1) = s and s = 2.
  use 2
  constructor
  · -- Show existence
    constructor
    · -- Show that f 1 = 2
      linarith
    · -- Show that 2 = 2
      rfl
  · -- Show uniqueness
    intro s h
    rcases h with ⟨h1s, h2s⟩
    -- Since s = 2 and f 1 = s, so f 1 = 2. Substitute into the equations
    -- Then we get s = 2
    linarith