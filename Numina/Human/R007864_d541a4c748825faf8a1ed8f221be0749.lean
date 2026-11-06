import Mathlib

/- At the candy store, a chocolate bar costs $c$ dollars and a vanilla bar costs $2$ dollars more than a chocolate bar. Jamie buys a chocolate bar and three vanilla bars, and Kevin buys five chocolate bars. How much money, in total, do Jamie and Kevin spend at the candy store in terms of $c$? -/
theorem algebra_20664 (c : ℝ) (h : c > 0) :
    (1 * c + 3 * (c + 2)) + (5 * c) = 9 * c + 6 := by 
  ring