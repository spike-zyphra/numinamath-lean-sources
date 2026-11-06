import Mathlib

/- A ferry boat shuttles tourists to an island every hour starting at 10 AM until its last trip, which starts at 3 PM. One day the boat captain notes that on the 10 AM trip there were 100 tourists on the ferry boat, and that on each successive trip, the number of tourists was 1 fewer than on the previous trip. How many tourists did the ferry take to the island that day?
(A) 585(B) 594(C) 672(D) 679(E) 694 -/
theorem algebra_94041 (n : ℕ) (h : n = 100) :
∑ i ∈ Finset.range 6, (n - i) = 585 := by 
--the number of tourists on the boat is 100 and decreases by 1 every hour. Hence the total number of tourists is 100 + 99 + 98 + 97 + 96 + 95 = 585
--suffices to solve by substitution
  simp [h]
  ring_nf