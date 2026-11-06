import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_276882 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = min (min (2 * x + 2) ((1 / 2) * x + 1)) (-((3 / 4) * x - 7))) :
  IsGreatest (range f) (17 / 5) := by
  constructor
  · -- Show that 17/5 is attainable, by x = 24/5
    use 24 / 5
    norm_num [h₀]
  · -- Show that 17/5 is the greatest value in the range
    intro y
    rintro ⟨x, hx⟩
    rw [h₀ x] at hx
    by_cases h1 : 2 * x + 2 ≤ (1 / 2) * x + 1 
    · -- Case 1: 2x+2 ≤ 1/2 x+1
      have h2 : min (2 * x + 2) ((1 / 2) * x + 1) = 2 * x + 2 := by apply min_eq_left h1 
      rw [h2] at hx 
      by_cases h3 : (2 * x + 2 : ℝ) ≤ -((3 / 4) * x - 7) 
      · -- Case 1a: 2x+2 ≤ -3/4 x+7
        have h4 : min (2 * x + 2) (-((3 / 4) * x - 7)) = 2 * x + 2 := by apply min_eq_left h3 
        rw [h4] at hx 
        linarith 
      · -- Case 1b: 2x+2 > -3/4 x+7
        have h4 : min (2 * x + 2) (-((3 / 4) * x - 7)) = -((3 / 4) * x - 7) := by apply min_eq_right (by linarith) 
        rw [h4] at hx 
        linarith 
    · -- Case 2: 2x+2 > 1/2 x+1 
      have h2 : min (2 * x + 2) ((1 / 2) * x + 1) = (1 / 2) * x + 1 := by apply min_eq_right (by linarith) 
      rw [h2] at hx 
      by_cases h3 : ( (1 / 2) * x + 1 : ℝ ) ≤ -((3 / 4) * x - 7) 
      · -- Case 2a: 1/2 x+1 ≤ -3/4 x+7 
        have h4 : min ((1 / 2) * x + 1) (-((3 / 4) * x - 7)) = ( (1 / 2) * x + 1 ) := by apply min_eq_left h3 
        rw [h4] at hx 
        linarith 
      · -- Case 2b: 1/2 x+1 > -3/4 x+7 
        have h4 : min ((1 / 2) * x + 1) (-((3 / 4) * x - 7)) = -((3 / 4) * x - 7) := by apply min_eq_right (by linarith) 
        rw [h4] at hx 
        linarith