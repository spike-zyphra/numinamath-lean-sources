import Mathlib

/- Show that $19^{19}$ cannot be written as the sum of a cube and a fourth power of integers. -/
theorem number_theory_99758 : ¬∃ x y, 19^19 = x^3 + y^4 := by
  push_neg
  rintro x y
  by_contra h
  -- consider the equation mod 13
  replace h : (19 ^ 19 : ZMod 13) = (x : ZMod 13)^3 + (y : ZMod 13)^4 := by
    norm_cast
    rw [h]
  -- a cube is 0,1,5,8,12 mod 13 by casework
  have h₀ (a : ZMod 13) : a^3 = 0 ∨ a^3 = 1 ∨ a^3 = 5 ∨ a^3 = 8 ∨ a^3 = 12 := by
    fin_cases a
    repeat
      simp
      norm_num
      norm_cast
  -- a 4th power is 0,1,3,9 mod 13 by casework
  have h₁ (a : ZMod 13) : a^4 = 0 ∨ a^4 = 1 ∨ a^4 = 3 ∨ a^4 = 9 := by
    fin_cases a
    repeat
      simp
      norm_num
      norm_cast
  -- try oute all combination from previous two lemmas, and see h is impossible
  obtain h₀ | h₀ | h₀ | h₀ | h₀ := h₀ (x : ZMod 13)
  all_goals (
    rw [h₀] at h
    obtain h₁ | h₁ | h₁ | h₁ := h₁ (y : ZMod 13)
    all_goals (
      rw [h₁] at h
      norm_cast at h
    )
  )