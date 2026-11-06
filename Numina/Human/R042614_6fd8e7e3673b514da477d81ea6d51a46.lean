import Mathlib

/-The radius of a circle is 2 inches. When the radius is doubled, by how many square inches is the area increased?  Express your  answer in terms of $\pi$.-/
theorem algebra_18900 (r : ℝ) (hr : r = 2) :
    π * (2 * r)^2 - π * r^2 = 12 * π := by
  -- substitute the r = 2
  rw [hr]
  ring_nf