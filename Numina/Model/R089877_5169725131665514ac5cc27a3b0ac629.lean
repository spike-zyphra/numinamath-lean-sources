import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_238146 {f : ℝ → ℝ}
  (hf : ∀ x, x ∈ Icc 0 (1/2) → f x = x + 1/2)
  (hf' : ∀ x, x ∈ Ioc (1/2) 1 → f x = 2 * (1 - x)) :
  ∃ x0 x1 x2 x3 x4 : ℝ, x0 ∈ Icc 0 1 ∧ x1 ∈ Icc 0 1 ∧ x2 ∈ Icc 0 1 ∧
  x3 ∈ Icc 0 1 ∧ x4 ∈ Icc 0 1 ∧ x0 ≠ x1 ∧ x0 ≠ x2 ∧ x0 ≠ x3 ∧ x0 ≠ x4 ∧
  x1 ≠ x2 ∧ x1 ≠ x3 ∧ x1 ≠ x4 ∧ x2 ≠ x3 ∧ x2 ≠ x4 ∧ x3 ≠ x4 ∧
  f x0 = x1 ∧ f x1 = x2 ∧ f x2 = x3 ∧ f x3 = x4 ∧ f x4 = x0 := by

  use (2 / 15 : ℝ)
  use (19 / 30 : ℝ)
  use (11 / 15 : ℝ)
  use (8 / 15 : ℝ)
  use (14 / 15 : ℝ)

  constructor
  · -- x0 ∈ [0, 1]
    exact ⟨by norm_num, by norm_num⟩

  constructor
  · -- x1 ∈ [0, 1]
    exact ⟨by norm_num, by norm_num⟩

  constructor
  · -- x2 ∈ [0, 1]
    exact ⟨by norm_num, by norm_num⟩

  constructor
  · -- x3 ∈ [0, 1]
    exact ⟨by norm_num, by norm_num⟩

  constructor
  · -- x4 ∈ [0, 1]
    exact ⟨by norm_num, by norm_num⟩

  constructor
  · -- x0 ≠ x1
    norm_num

  constructor
  · -- x0 ≠ x2
    norm_num

  constructor
  · -- x0 ≠ x3
    norm_num

  constructor
  · -- x0 ≠ x4
    norm_num

  constructor
  · -- x1 ≠ x2
    norm_num

  constructor
  · -- x1 ≠ x3
    norm_num

  constructor
  · -- x1 ≠ x4
    norm_num

  constructor
  · -- x2 ≠ x3
    norm_num

  constructor
  · -- x2 ≠ x4
    norm_num

  constructor
  · -- x3 ≠ x4
    norm_num

  constructor
  · -- f x0 = x1
    have h0 : (2 / 15 : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by
      exact ⟨by norm_num, by norm_num⟩
    rw [hf (2 / 15) h0]
    norm_num

  constructor
  · -- f x1 = x2
    have h1 : (19 / 30 : ℝ) ∈ Ioc (1 / 2 : ℝ) 1 := by
      exact ⟨by norm_num, by norm_num⟩
    rw [hf' (19 / 30) h1]
    norm_num

  constructor
  · -- f x2 = x3
    have h2 : (11 / 15 : ℝ) ∈ Ioc (1 / 2 : ℝ) 1 := by
      exact ⟨by norm_num, by norm_num⟩
    rw [hf' (11 / 15) h2]
    norm_num

  constructor
  · -- f x3 = x4
    have h3 : (8 / 15 : ℝ) ∈ Ioc (1 / 2 : ℝ) 1 := by
      exact ⟨by norm_num, by norm_num⟩
    rw [hf' (8 / 15) h3]
    norm_num

  · -- f x4 = x0
    have h4 : (14 / 15 : ℝ) ∈ Ioc (1 / 2 : ℝ) 1 := by
      exact ⟨by norm_num, by norm_num⟩
    rw [hf' (14 / 15) h4]
    norm_num