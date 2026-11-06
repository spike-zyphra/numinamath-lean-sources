import Mathlib

theorem algebra_304761 (x y : ℝ) (h : abs x + abs y = 1) :
    y - 2 * x ∈ Set.Icc (-2) 2 := by
  have h1 : -2 ≤ y - 2 * x := by 
    cases' abs_cases x with hx hx
    · -- Case x ≥ 0
      cases' abs_cases y with hy hy
      · -- Case y ≥ 0
        linarith
      · -- Case y < 0
        linarith
    · -- Case x < 0
      cases' abs_cases y with hy hy
      · -- Case y ≥ 0
        linarith
      · -- Case y < 0
        linarith

  have h2 : y - 2 * x ≤ 2 := by 
    cases' abs_cases x with hx hx
    · -- Case x ≥ 0
      cases' abs_cases y with hy hy
      · -- Case y ≥ 0
        linarith
      · -- Case y < 0
        linarith
    · -- Case x < 0
      cases' abs_cases y with hy hy
      · -- Case y ≥ 0
        linarith
      · -- Case y < 0
        linarith
  constructor
  · -- Show that -2 ≤ y - 2 * x
    linarith
  · -- Show that y - 2 * x ≤ 2
    linarith