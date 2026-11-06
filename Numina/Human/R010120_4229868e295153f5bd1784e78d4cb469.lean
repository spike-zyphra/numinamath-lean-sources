import Mathlib

/- Three friends are driving to New York City and splitting the gas cost equally. At the last minute, 2 more friends joined the trip. The cost of gas was then evenly redistributed among all of the friends. The cost for each of the original 3 decreased by $\$$11.00. What was the total cost of the gas, in dollars? -/
theorem algebra_14180 {x : ℝ} (hx : x ≠ 0) (h : (x / 3 - 11) = x / 5) :
    x = 82.50 := by
  field_simp at h
  ring_nf at h ⊢
  linarith