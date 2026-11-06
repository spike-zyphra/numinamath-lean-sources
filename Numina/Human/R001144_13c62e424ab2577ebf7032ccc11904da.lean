import Mathlib

/- What is the sixth term in the geometric sequence $\frac{27}{125}, \frac{9}{25}, \frac{3}{5},\ldots$?  Express your answer as a common fraction.-/
theorem algebra_20712 (a : ℕ → ℝ) (r : ℝ) (ha : ∀ n, a (n + 1) = r * a n)
    (ha0 : a 0 = 27 / 125) (ha1 : a 1 = 9 / 25) (ha2 : a 2 = 3 / 5) :
    a 5 = 25 / 9 := by
  have := ha 0
  rw [ha0, ha1, mul_comm] at this
  symm at this
  apply_fun ((27 / 125)⁻¹ * ·) at this
  -- With common ratio $\frac{5}{3}$, and first term $\frac{27}{125}$,
  have : r = 5 / 3 := by linear_combination this
  -- we simply take: $\frac{27}{125}\times\left(\frac{5}{3}\right)^{5}$
  -- which yields $\boxed{\frac{25}{9}}.$
  norm_num [ha 4, ha 3, ha 2, ha2, this]
