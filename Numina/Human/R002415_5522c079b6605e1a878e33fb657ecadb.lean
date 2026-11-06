import Mathlib

/- For each positive integer n, the mean of the first
   n terms of a sequence is n. What is the 2008th term of the sequence?
   (A) 2008(B) 4015(C) 4016(D) 4030056(E) 4032064 -/
theorem algebra_93059 (a : ℕ → ℝ) (h : ∀ n, ∑ i in Finset.range n, a i = n  * n) :
a 2007 = 4015 := by
  -- The only possible sequence with this result is the sequence of odd integers.
  have h : ∀ n, a n = 2 * n + 1 := by
    intro n
    /- By subtracting the sum of the first n + 1 elements by the sum of the first n elements to 
       see that the n-th element is equal to (n + 1)^2 - n^2 = 2n + 1 -/
    rw [← Finset.sum_range_succ_sub_sum a]
    rw [h (n + 1), h n]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [h 2007]
  rw [Nat.cast_ofNat]
  ring