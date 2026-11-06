import Mathlib

theorem number_theory_13118 :
   IsLeast { x : ℤ  | ∃ p g : ℤ ,(0<x) ∧ p * 300 + g * 210 = x} 30 := by
  constructor
  · -- Show that 30 is in the set with specific p and g
    use -2, 3
    all_goals norm_num
  · -- We need to show that 30 is the smallest
    intro x hx
    rcases hx with ⟨p, g, hx1, h_eq⟩
    omega