import Mathlib
/-A contest has six problems worth seven points each. On any given problem, a contestant can score either 0,1 , or 7 points. How many possible total scores can a contestant achieve over all six problems?-/

-- Function to calculate all possible total scores for a given number of problems
def calculatePossibleTotalScores (num_problems : ℕ) : Finset ℕ :=
  -- Let N be the number of problems
  let N := num_problems
  -- Iterate through n7 (number of problems scoring 7 points) from 0 to N
  (Finset.range (N + 1)).biUnion fun n7 =>
    -- For each n7, n1 (number of problems scoring 1 point) can range from 0 up to N - n7.
    -- The number of elements in this range is (N - n7 + 1).
    (Finset.range (N - n7 + 1)).image fun n1 =>
      -- Calculate the total score for this combination of n1 and n7
      n1 + 7 * n7


-- Get the count of these distinct scores
theorem combinatorics_609531 : 
  (calculatePossibleTotalScores 6).card = 28 := by 
  unfold calculatePossibleTotalScores
  rfl

