import Mathlib

/- The NASA Space Shuttle transports material to the International Space Station at a cost of $\$22,\!000$ per kilogram. What is the number of dollars in the cost of transporting a 250 g control module? -/
theorem algebra_10877 (cost : ℝ → ℝ) (hcost : cost = fun x => 22000 * x) :
    cost (250 / 1000) = 5500 := by
  rw [hcost]; norm_num