import Mathlib

theorem algebra_11540 : IsGreatest {x | ∃ a b : ℝ, 3*a+2*b≤7 ∧ 2*a+4*b≤8 ∧ x=a+b} (11/4) := by 
  constructor
  · -- Show that 11/4 belongs to the set
    use 3 / 2, 5 / 4
    norm_num
  · -- Show that any value in the set is <= 11/4
    intro x hx
    rcases hx with ⟨a, b, h1, h2, h3⟩
    linarith