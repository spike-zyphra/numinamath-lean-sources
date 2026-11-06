import Mathlib

theorem algebra_12054 : IsGreatest {x | ∃ a b : ℤ, x = a * b ∧ a + b = 246} 15129 := by 
  constructor
  · -- Show that 15129 is in the set
    use 123, 123
    all_goals norm_num
  · -- Show that 15129 is an upper bound
    intro x hx
    rcases hx with ⟨a, b, h1, h2⟩
    have h3 : b = 246 - a := by linarith
    rw [h3] at h1
    have h4 : (a - 123) ^ 2 ≥ 0 := by
      apply sq_nonneg
    nlinarith