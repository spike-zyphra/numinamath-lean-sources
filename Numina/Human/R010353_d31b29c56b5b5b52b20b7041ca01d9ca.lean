import Mathlib

/-- The sums of three whole numbers taken in pairs are 12, 17, and 19. What is the middle number?
    (A) 4(B) 5(C) 6(D) 7(E) 8 -/
theorem algebra_93690 (a b c : ℤ) (h₀ : a + b = 12) (h₁ : a + c = 17) (h₂ : b + c = 19) :
    b = 7 ∧ a < b ∧ b < c := by
  -- Let us call the integers a <= b <= c. Clearly, we must have a + b = 12, a + c = 17, and b + c = 19,
  -- otherwise the orders would not work out.
  -- Subtracting the first two equations, we get c - b = 5.
  have : c - b = 5 := by linarith
  -- Inserting this in the third one yields 2b + 5 = 19,
  have : 2 * b + 5 = 19 := by linarith
  -- hence b = 7.
  obtain rfl : b = 7 := by linarith
  -- Then due to b + c = 19, we have c = 12,
  obtain rfl : c = 12 := by linarith
  -- and due to a + c = 17, we have a = 5.
  obtain rfl : a = 5 := by linarith
  tauto