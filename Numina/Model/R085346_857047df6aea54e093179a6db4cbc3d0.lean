import Mathlib

theorem algebra_3329 :
  IsGreatest {x | ∃ a b c : ℝ, a + 2 * b + c = 4 ∧ x = a * b + b * c + c * a} 4 := by
  constructor
  · -- Show that 4 is achievable, using a = 2, b = 0, c = 2
    use 2, 0, 2
    norm_num 
  · -- Show that no value greater than 4 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, h1, h2⟩
    have h3 : a + c = 4 - 2 * b := by linarith
    nlinarith [sq_nonneg (a - 2 - c), sq_nonneg (a - c), sq_nonneg (b), sq_nonneg (a + c - 2)]