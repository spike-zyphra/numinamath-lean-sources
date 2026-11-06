import Mathlib

/- A deck of cards has only red cards and black cards. The probability of a randomly chosen card being red is 1/3​. 
When 4 black cards are added to the deck, the probability of choosing red becomes 1/4​. How many cards were in the 
deck originally?
(A) 6(B) 9(C) 12(D) 15(E) 18-/
theorem algebra_94230 {n : ℕ} (h : (n + 4) * (1 / 4 : ℚ) = n * (1 / 3 : ℚ)) :
n = 12 := by {
  field_simp at h -- Eliminate denominators in hypothesis
  ring_nf at h
  norm_cast at h -- Reduce the hypothesis to the equation 12 + n*3 = n*4 in ℕ.
  -- Now we can deduce the claim by simple algebraic manipulations.
  calc n = (n*4 - n*3) := by rw [←Nat.mul_sub_left_distrib]; norm_num
       _ = (12 + n*3 - n*3) := by rw [h]
       _ = 12 := by simp
}