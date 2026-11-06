import Mathlib

theorem algebra_96714 (s ss : Finset ℤ) (hs : s ={-7, -5, -1, 1, 3}) 
(hss : ss = {x : ℤ | ∃ a : s , ∃ b : s , x = a * b}) :
IsLeast (ss) (-21) := by

  unfold IsLeast
  constructor
  · rw[hss]
    simp
    use -7
    constructor
    · rw[hs]
      simp
    · use 3
      constructor
      · rw[hs]
        simp
      · ring
  · unfold lowerBounds
    rw[hss]
    intro x hx
    simp at hx
    rcases hx with ⟨a, ha, b, hb, heq⟩
    rw[hs] at ha hb
    simp at ha hb
    rcases ha with (rfl | rfl | rfl | rfl | rfl)
    all_goals
      rcases hb with (rfl | rfl | rfl | rfl | rfl)
      all_goals
        omega