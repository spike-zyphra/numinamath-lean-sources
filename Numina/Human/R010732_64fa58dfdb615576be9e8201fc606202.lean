import Mathlib

/-100 people who were surveyed and asked the question: ``Is fuchsia kinda pink, or purply?'' Of them, 60 believe that fuchsia is ``kinda pink'' and 27 believe it is both ``kinda pink,'' and also ``purply.''  Another 17 think that fuchsia is neither ``kinda pink'' nor ``purply.''

How many of those 100 people believe that fuchsia is ``purply''?

The final answer is $ \boxed{50} $-/
theorem algebra_16612 (total_people : ℕ) (h₀ : total_people = 100)
    (kinda_pink : ℕ) (purply : ℕ) (h₁ : kinda_pink = 60) (both : ℕ)
    (h₂ : both = 27) (neither : ℕ) (h₃ : neither = 17)
    (h : kinda_pink + purply - both + neither = total_people) : purply = 50 := by
      -- Since total number of people is 100, and the number of people who believe kinda pink
      -- add the number of people who believe purply minus the number of people who believe both
      -- add the number of people who believe neither is 100, so the number of people who believe
      -- purple is 50.
      rw [Nat.sub_add_comm (by omega)] at h
      simp [h₁, h₂, h₃] at h
      linarith
