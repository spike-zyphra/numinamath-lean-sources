import Mathlib

/- Paint is to be mixed so that the ratio of red paint to white paint is 3 to 2. If Ben wants to make 30 cans of the mixture and all cans hold the same volume of paint, how many cans of red paint will he need? -/
theorem algebra_12478 {x y : ℕ} (h : x * 2 = y * 3) (h' : x + y = 30) :
    x = 18 := by
  ring_nf at h h'
  omega