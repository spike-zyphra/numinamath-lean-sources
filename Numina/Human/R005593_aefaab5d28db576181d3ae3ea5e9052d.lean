import Mathlib

/-A restaurant has some number of seats, arranged in a line. Its customers are in parties arranged in a queue. To seat its customers, the restaurant takes the next party in the queue and attempts to seat all of the party's member(s) in a contiguous block of unoccupied seats. If one or more such blocks exist, then the restaurant places the party in an arbitrarily selected block; otherwise, the party leaves.

Suppose the queue has parties of sizes $6,4,2,5,3,1$ from front to back, and all seats are initially empty. What is the minimal number of seats the restaurant needs to guarantee that it will seat all of these customers?-/

-- The sequence of party sizes from front to back of the queue
def PartySizes : List ℕ := [6, 4, 2, 5, 3, 1]

-- Recursive helper function to check if all parties can be guaranteed seats.
-- It models the worst-case scenario for available block sizes.

def check_guaranteed_seating_aux (parties : List ℕ) (free_seats num_regions : ℕ) : Bool :=
  match parties with
  | [] => true -- Base case: All parties have been seated
  | p :: ps => -- Recursive step: Current party of size p, remaining parties ps
    let largest_block_min_size := Int.ceil (Rat.div free_seats num_regions)
    if largest_block_min_size < p then
      false -- Cannot guarantee seating current party p
    else
      -- Party p is seated. Update state for the next party.
      check_guaranteed_seating_aux ps (free_seats - p) (num_regions + 1)

-- Main function to start the check.
-- Initially, all 'total_seats' are in 1 contiguous region.
def check_guaranteed_seating (total_seats : ℕ) (parties : List ℕ) : Bool :=
  check_guaranteed_seating_aux parties total_seats 1

-- Theorem: 29 seats are sufficient to guarantee seating for all parties.
theorem twenty_nine_seats_are_sufficient :
  check_guaranteed_seating 29 PartySizes = true := by
  native_decide -- Lean can compute this boolean function directly.
  -- For manual check:
  -- check_guaranteed_seating_aux [6, 4, 2, 5, 3, 1] 29 1
  -- P=6: ceil(29/1)=29. 29≥6. OK. Call aux [4,2,5,3,1] (29-6)=23 (1+1)=2
  -- P=4: ceil(23/2)=12. 12≥4. OK. Call aux [2,5,3,1] (23-4)=19 (2+1)=3
  -- P=2: ceil(19/3)=7.  7≥2.  OK. Call aux [5,3,1] (19-2)=17 (3+1)=4
  -- P=5: ceil(17/4)=5.  5≥5.  OK. Call aux [3,1] (17-5)=12 (4+1)=5
  -- P=3: ceil(12/5)=3.  3≥3.  OK. Call aux [1] (12-3)=9 (5+1)=6
  -- P=1: ceil(9/6)=2.   2≥1.  OK. Call aux [] (9-1)=8 (6+1)=7
  -- Parties list is empty: true.

-- Theorem: 28 seats are insufficient to guarantee seating for all parties.
theorem twenty_eight_seats_are_insufficient :
  check_guaranteed_seating 28 PartySizes = false := by
  native_decide
  -- For manual check:
  -- check_guaranteed_seating_aux [6, 4, 2, 5, 3, 1] 28 1
  -- P=6: ceil(28/1)=28. 28≥6. OK. Call aux [4,2,5,3,1] (28-6)=22 (1+1)=2
  -- P=4: ceil(22/2)=11. 11≥4. OK. Call aux [2,5,3,1] (22-4)=18 (2+1)=3
  -- P=2: ceil(18/3)=6.  6≥2.  OK. Call aux [5,3,1] (18-2)=16 (3+1)=4
  -- P=5: ceil(16/4)=4.  4<5.  Returns false.

-- The minimal number of seats is 29, as 29 are sufficient and 28 are not.
theorem minimal_seats_is_29 :
  check_guaranteed_seating 29 PartySizes = true ∧
  check_guaranteed_seating 28 PartySizes = false := by
  constructor
  · exact twenty_nine_seats_are_sufficient
  · exact twenty_eight_seats_are_insufficient