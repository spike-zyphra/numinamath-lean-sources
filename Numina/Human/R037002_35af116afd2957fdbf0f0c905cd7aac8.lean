import Mathlib

/- The sum of six consecutive positive integers is 2013. What is the largest of these six integers?
(A) 335 (B) 338 (C) 340 (D) 345 (E) 350-/
theorem algebra_97732 (n : ℕ) (h₁ : n + (n + 1) + (n + 2) + (n + 3) + (n + 4) + (n + 5) = 2013) :
n + 5 = 338 := by {
  -- Add all the 6 terms together
  ring_nf at h₁
  -- Now we rearrange the expression n + 5 that we want to calculate so that we can use the hypothesis
  calc n + 5 = (n + 5)*6 / 6 := by norm_num
           _ = (n * 6 + 5 * 6) / 6 := by rw [Nat.right_distrib]
           _ = (15 + n * 6 - 15 + 5 * 6) / 6 := by rw [Nat.add_sub_cancel_left]
           _ = (2013 - 15 + 5 * 6) / 6 := by rw [h₁] -- Plug in the hypothesis
           _ = 338 := by norm_num -- Evaluate the expression
}