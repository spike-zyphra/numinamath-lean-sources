import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_319875 (x y : ℝ) (h : abs (x + y) < abs (x - y)) :
    (x < 0 ∧ y > 0) ∨ (x > 0 ∧ y < 0) := by
  by_cases h1 : x + y ≥ 0
  · -- Case where x + y ≥ 0
    by_cases h2 : x - y ≥ 0
    · -- Case where x + y ≥ 0 and x - y ≥ 0
      rw [abs_of_nonneg h1, abs_of_nonneg h2] at h
      have h3 : y < 0 := by linarith
      have h4 : x > 0 := by nlinarith
      right
      exact ⟨by linarith, by linarith⟩
    · -- Case where x + y ≥ 0 and x - y < 0
      rw [abs_of_nonneg h1, abs_of_neg (show x - y < 0 by linarith)] at h
      have h5 : x < 0 := by linarith
      have h6 : y > 0 := by nlinarith
      left
      exact ⟨by linarith, by linarith⟩
  · -- Case where x + y < 0
    by_cases h2 : x - y ≥ 0
    · -- Case where x + y < 0 and x - y ≥ 0
      rw [abs_of_neg (show x + y < 0 by linarith), abs_of_nonneg h2] at h
      have h7 : x > 0 := by linarith
      have h8 : y < 0 := by nlinarith
      right
      exact ⟨by linarith, by linarith⟩
    · -- Case where x + y < 0 and x - y < 0
      rw [abs_of_neg (show x + y < 0 by linarith), abs_of_neg (show x - y < 0 by linarith)] at h
      have h9 : y > 0 := by linarith
      have h10 : x < 0 := by nlinarith
      left
      exact ⟨by linarith, by linarith⟩