import Mathlib

/- Which one of the following integers can be expressed as the sum of 100 consecutive positive integers?
(A) 1,⁣627,⁣384,⁣950 (B) 2,⁣345,⁣678,⁣910 (C) 3,⁣579,⁣111,⁣300 (D) 4,⁣692,⁣581,⁣470 (E) 5,⁣815,⁣937,⁣260-/
theorem number_theory_93369 : ∃ k, 1627384950 = ∑ i ∈ Finset.range 100, ((k + 1) + i) := by {
  -- The sum of the first 100 numbers is 5050, and this means that an integer is the sum of 100 consecutive integers iff
  -- it is 50 mod 100 (and at least 5050). To determine k, we evaluate the sum, which tells us that n = 5050 + 100*k,
  -- and then solve for k.
  use (1627384950 - 5050) / 100 
  simp [Finset.sum_range_succ, Nat.add_comm, Nat.add_sub_assoc]
}