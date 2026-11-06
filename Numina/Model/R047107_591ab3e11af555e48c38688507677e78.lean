import Mathlib

open Finset


theorem number_theory_9371 (x y : ℕ → ℤ)
    (hx1 : x 1 = 1) (hy1 : y 1 = 1)
    (hxn : ∀ k ≥ 2, x k = x (k - 1) + 1 - 5 * ⌊(k - 1) / 5⌋₊ + 5 * ⌊(k - 2) / 5⌋₊)
    (hy : ∀ k ≥ 2, y k = y (k - 1) + ⌊(k - 1) / 5⌋₊ - ⌊(k - 2) / 5⌋₊) :
    x 2008 = 3 ∧ y 2008 = 402 := by

  have h1 : ∀ k : ℕ, x (k + 1) = (k + 1 : ℤ) - 5 * ((k : ℤ) / 5) := by
    intro k
    induction k with
    | zero =>
      norm_num [hx1]
    | succ k ih =>
      have h2 := hxn (k + 2) (by linarith)
      simp [show k + 2 = (k + 1) + 1 by omega] at h2 ⊢
      rw [h2]
      rw [ih]
      omega


  have h2 : ∀ k : ℕ, y (k + 1) = ((k : ℤ) / 5) + 1 := by
    intro k
    induction k with
    | zero =>
      norm_num [hy1]
    | succ k ih =>
      have h3 := hy (k + 2) (by linarith)
      simp [show k + 2 = (k + 1) + 1 by omega] at h3 ⊢
      rw [h3]
      rw [ih]
      omega

  constructor
  · -- Compute x 2008
    have hx2008 : x 2008 = 3 := by
      have h3 : x 2008 = (2008 : ℤ) - 5 * ((2007 : ℤ) / 5) := by
        specialize h1 2007
        norm_num at h1 ⊢
        linarith
      norm_num at h3 ⊢
      linarith
    exact hx2008
  · -- Compute y 2008
    have hy2008 : y 2008 = 402 := by
      have h3 : y 2008 = ((2007 : ℤ) / 5) + 1 := by
        specialize h2 2007
        norm_num at h2 ⊢
        linarith
      norm_num at h3 ⊢
      linarith
    exact hy2008