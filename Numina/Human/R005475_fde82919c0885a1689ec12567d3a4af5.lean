import Mathlib 

/- A cat is going up a stairwell with ten stairs. However, instead of walking up the stairs one at a time, the cat jumps, going either two or three stairs up at each step (though if necessary, it will just walk the last step). How many different ways can the cat go from the bottom to the top?
-/
def ways_to_stair : Nat → Nat
  | 0 => 1  -- There is one "way" to be at the bottom (stair 0): by starting there.
  | 1 => 0  -- It's impossible to land on stair 1 with jumps of 2 or 3 from stair 0.
  | 2 => 1  -- One way to land on stair 2: a single jump of 2 from stair 0.
  -- The recursive step for any other stair `n`. A cat must have arrived from
  -- stair `n-2` (with a jump of 2) or stair `n-3` (with a jump of 3).
  | n + 3 => ways_to_stair (n + 1) + ways_to_stair n

def total_ways_to_top : Nat :=
  ways_to_stair 10 + ways_to_stair 9

theorem combinatorics_608432 : total_ways_to_top = 12 := by 
rfl