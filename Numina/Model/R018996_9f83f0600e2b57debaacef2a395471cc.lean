import Mathlib

theorem algebra_187941 (a : ℝ) (ha : a = 1 ∨ a = 4 ∨ a = 2 ∨ a = 3) :
    (∃! x : ℝ, ∃! y : ℝ, (x - 3)^2 + y^2 = 1 ∧ y - 1 = 2 * (x - 3)^6 + abs (x - 3)) ∨
    (∃! x : ℝ, ∃! y : ℝ, (x - 3)^2 + y^2 = 1 ∧ y + 1 = abs (x - 3)) := by 
  left
  use 3
  constructor
  · -- Show that 3 is the x value
    use 1
    constructor
    · -- Show that (3,1) is a solution
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Show that it's unique
      intro y h
      rcases h with ⟨h_eq1, h_eq2⟩
      have hy : y = 1 := by
        norm_num [abs_of_nonneg, abs_of_nonpos] at h_eq1 h_eq2 ⊢
        nlinarith
      exact hy
  · -- Show that 3 is unique
    intro x hx
    rcases hx with ⟨y, hy1, hy2⟩
    have h_eq1 : (x - 3)^2 + y^2 = 1 := by 
      linarith [hy1]
    have h_eq2 : y - 1 = 2 * (x - 3)^6 + abs (x - 3) := by
      linarith [hy2]
    -- Prove x = 3 and y = 1
    have h2 : y ≥ 1 := by
      have h3 : 2 * (x - 3)^6 + abs (x - 3) ≥ 0 := by
        positivity
      linarith
    -- Show y = 1 from equation.
    have hy : y = 1 := by
      have h4 : y ≤ 1 := by
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 3), abs_nonneg (x - 3), 
          sq_nonneg (y - 1), sq_nonneg (y + 1), abs_nonneg (x - 3)]
      nlinarith
    -- Show x = 3 from equation.
    have hx : x = 3 := by
      rw [hy] at h_eq1
      nlinarith [sq_nonneg (x - 3), abs_nonneg (x - 3)]
    exact hx