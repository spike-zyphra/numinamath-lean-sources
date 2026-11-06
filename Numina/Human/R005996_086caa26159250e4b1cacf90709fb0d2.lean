import Mathlib
/- A rubber band is 4 inches long. An ant begins at the left end. Every minute, the ant walks one inch along rightwards along the rubber band, but then the band is stretched (uniformly) by one inch. For what value of $n$ will the ant reach the right end during the $n$th minute? -/

-- the trick of answering this question is to spot that relative distance of ant travel to band lenth is much simpler to handle than considering absolute distance travel, thus defining the following:

noncomputable def S (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, (1 / (↑(i + 4)))

theorem logic_puzzle_611015 : S 6 < 1 ∧ S 7 ≥ 1 :=
by 
  constructor
  -- show that the ant don't reach the right end on minute 6
  · dsimp [S] 
    linarith
  -- show that the ant do reach the right end before minute 7
  · dsimp [S]
    linarith



