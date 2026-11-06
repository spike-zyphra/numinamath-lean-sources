import Mathlib

/- What number must we add to $3-5i$ to get $2+7i$? Here, $i^2 = -1.$ -/
theorem algebra_14506 (x : ℂ) (h : x + (3 - 5 * .I) = 2 + 7 * .I) :
    x = -1 + 12 * .I := by
  have h' : x = -1 + 12 * .I := by linear_combination h
  exact h'