import Mathlib

theorem algebra_6056 : IsLeast {x | ∃ t : ℝ, x = 12 * t ^ 2 - 60 * t + 81} 6 := by 
  constructor
  · -- Show that 6 is in the set
    use 5 / 2
    norm_num 
  · -- Show that 6 is the least in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h_eq : 12 * t ^ 2 - 60 * t + 81 = 12 * (t - 5 / 2) ^ 2 + 6 := by 
      ring
    rw [h_eq] at ht 
    have h1 : 12 * (t - 5 / 2) ^ 2 ≥ 0 := by 
      have h5 : (t - 5 / 2) ^ 2 ≥ 0 := sq_nonneg (t - 5 / 2)
      nlinarith [h5]
    linarith [ht, h1]