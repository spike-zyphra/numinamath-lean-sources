import Mathlib

theorem algebra_10750
  (x₀ y₀ m c : ℝ) -- let (x₀, y₀) be the intersection, and let the second line have equation y = mx + c
  (l1 : y₀ = 2 * x₀ + 5) -- (x₀, y₀) lies on line
  (l2 : y₀ = m * x₀ + c) -- (x₀, y₀) lies on line 2
  (perpendicular : m * 2 = -1) -- lines 1 and 2 are perpendicular
  (l2_contains_55 : 5 = m * 5 + c) -- (5, 5) lies on line 2
: x₀ = 1 ∧ y₀ = 7 := by

  have hm : m = -1 / 2 := by linarith

  have hc : c = 15 / 2 := by 
    rw [hm] at l2_contains_55
    linarith

  have hx₀ : x₀ = 1 := by 
    rw [hm, hc] at l2
    linarith [l1, l2]

  have hy₀ : y₀ = 7 := by 
    linarith [l1, hx₀]

  exact ⟨hx₀, hy₀⟩