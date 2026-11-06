import Mathlib

theorem algebra_15652 {g : ℝ → ℝ} (hg : ∀ x, x < 0 → g x = 3 * x + 6)
    (hg' : ∀ x, x ≥ 0 → g x = 2 * x - 13) (x : ℝ) :
    g x = 3 ↔ x = -1 ∨ x = 8 := by
  constructor
  · -- Forward direction: If g(x) = 3, then x = -1 or x = 8
    intro hx
    by_cases h : x < 0
    · -- Case 1: x < 0
      have hx1 : g x = 3 * x + 6 := hg x h
      rw [hx1] at hx
      have h1 : x = -1 := by linarith
      left
      exact h1
    · -- Case 2: x ≥ 0
      have h2 : x ≥ 0 := by linarith
      have hx2 : g x = 2 * x - 13 := hg' x h2
      rw [hx2] at hx
      have h2' : x = 8 := by linarith
      right
      exact h2'
  · -- Backward direction: If x = -1 or x = 8, then g(x) = 3
    rintro (h | h)
    · -- Case 1: x = -1
      rw [h]
      norm_num [hg]
    · -- Case 2: x = 8
      rw [h]
      norm_num [hg']