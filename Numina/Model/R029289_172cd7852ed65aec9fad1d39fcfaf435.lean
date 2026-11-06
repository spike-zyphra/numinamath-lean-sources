import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_302851 (f g h : ℝ → ℝ)
  (hf : f = λ x => 2 * x) (hg : g = λ x => x + 2) (hh : h = λ x => -2 * x + 12)
  (y : ℝ → ℝ) (hy : y = λ x => min (min (f x) (g x)) (h x)) :
  IsGreatest (range y) (16 / 3) := by
  have h1 : ∀ x, y x = min (min (f x) (g x)) (h x) := by
    intro x 
    rw [hy]
  have h2 : 16 / 3 ∈ range y := by 
    use 10 / 3 
    rw [h1]
    rw [hf, hg, hh]
    norm_num 
  have h3 : ∀ r ∈ range y, r ≤ 16 / 3 := by 
    intro r hr 
    rcases hr with ⟨x, hx⟩ 
    rw [h1 x] at hx 
    rw [hf, hg, hh] at hx 
    by_cases h1 : (2 * x : ℝ) ≤ (x + 2 : ℝ)
    · -- When 2 * x ≤ x + 2, which is when x ≤ 2 
      have min1 : min (2 * x) (x + 2) = (2 * x : ℝ) := by 
        apply min_eq_left 
        linarith 
      by_cases h2 : (2 * x : ℝ) ≤ (-2 * x + 12 : ℝ)
      · -- When 2 * x ≤ -2 * x + 12, which is when x ≤ 3 
        have min2 : min (2 * x) (-2 * x + 12) = (2 * x : ℝ) := by 
          apply min_eq_left 
          linarith 
        rw [min1, min2] at hx 
        linarith 
      · -- When 2 * x > -2 * x + 12, which is when x > 3 
        have min2 : min (2 * x) (-2 * x + 12) = (-2 * x + 12 : ℝ) := by 
          apply min_eq_right 
          linarith 
        rw [min1, min2] at hx 
        linarith 
    · -- When 2 * x > x + 2, which is when x > 2 
      have min1 : min (2 * x) (x + 2) = (x + 2 : ℝ) := by 
        apply min_eq_right 
        linarith 
      by_cases h2 : (x + 2 : ℝ) ≤ (-2 * x + 12 : ℝ)
      · -- When x + 2 ≤ -2 * x + 12, which is when x ≤ 10 / 3 
        have min2 : min (x + 2) (-2 * x + 12) = (x + 2 : ℝ) := by 
          apply min_eq_left 
          linarith 
        rw [min1, min2] at hx 
        linarith 
      · -- When x + 2 > -2 * x + 12, which is when x > 10 / 3 
        have min2 : min (x + 2) (-2 * x + 12) = (-2 * x + 12 : ℝ) := by 
          apply min_eq_right 
          linarith 
        rw [min1, min2] at hx 
        linarith 
  exact ⟨h2, h3⟩