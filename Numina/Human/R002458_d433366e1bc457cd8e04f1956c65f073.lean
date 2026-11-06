import Mathlib

/- In a bag of marbles, 3553​ of the marbles are blue and the rest are red. If the number of red marbles is doubled 
and the number of blue marbles stays the same, what fraction of the marbles will be red?
(A) 25(B) 37(C) 47(D) 35(E) 45-/
theorem algebra_93679 {b r : ℕ} (hb : b ≠ 0) (hr : r ≠ 0)
(h : (b : ℚ) / (b + r) = 3 / 5) :
(2 * (r : ℚ)) / (b + 2 * r) = 4 / 7 := by {
  -- We show that the ratio between blue and red is 3 : 2. This is a simple algebraic manipulcation from the assumptions.
  have h₁ : (b : ℚ) = 3 * r / 2 := by {
    -- Eliminate denominators in the hypothesis
    field_simp at h
    ring_nf at h
    calc (b : ℚ) = b * 2 / 2 := by norm_num
               _ = (b * 5 - b * 3) / 2 := by ring
               _ = 3 * r / 2 := by rw [h]; ring -- Here we use the hypothesis
  }
  rw [h₁] -- Replace b by 3*r/2
  field_simp -- Eliminate denominators
  ring -- Deduce the claim
}