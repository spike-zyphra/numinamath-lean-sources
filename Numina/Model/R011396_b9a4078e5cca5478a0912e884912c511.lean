import Mathlib
open Real

theorem inequalities_243621 :
  IsLeast {x : ℝ | ∀ a > 0, x^2 < 1 + a} (-1) := by
  constructor 
  · -- Show that -1 is in the set
    intro a ha 
    norm_num 
    all_goals
    nlinarith 
  · -- Show that -1 is the minimum 
    intro x hx
    have h : ∀ a > 0, x^2 < 1 + a := by
      simpa using hx 
    by_contra h' 
    push_neg at h'
    -- Assume for contradiction that x < -1
    have h1 : x < -1 := by linarith 
    have h2 : x^2 > 1 := by 
      nlinarith 
    have h3 : x^2 < 1 + (x^2 - 1) := by 
      have h_a : x^2 - 1 > 0 := by 
        nlinarith 
      specialize h (x^2 - 1) h_a 
      simpa using h 
    nlinarith