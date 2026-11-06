import Mathlib

/- Find $\left \lceil \frac{12}{7} \cdot \frac{-29}{3}\right\rceil - \left\lfloor \frac{12}{7} \cdot \left \lfloor \frac{-29}{3}\right \rfloor \right \rfloor$. -/
theorem algebra_16554 : ⌈(12 / 7 * -29 / 3 : ℝ)⌉ - ⌊((12 / 7 : ℝ) * ⌊(-29 / 3 : ℝ)⌋)⌋ = 2 := by
  -- Use ⌈-a⌉ = -⌊a⌋.
  norm_num [Int.ceil_neg]
