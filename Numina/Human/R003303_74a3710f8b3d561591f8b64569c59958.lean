import Mathlib

/- $2+$ $[$ higher degree equations (miscellaneous). ]

Solve the equation $\left[x^{3}\right]+\left[x^{2}\right]+[x]=\{x\}-1$.

# -/
theorem algebra_167935 (x : ℤ) (h : ⌊x^3⌋ + ⌊x^2⌋ + ⌊x⌋ = (x - ⌊x⌋) - 1) : x = -1 := by
  -- Since x is an integer, x = ⌊x⌋
  simp only [Int.floor_int, id_eq, sub_self, zero_sub, Int.reduceNeg] at h
  -- Solve the resulting cubic
  obtain hx | hx' := mul_eq_zero.mp (show (x + 1) * (x^2 + 1) = 0 by nlinarith) <;> nlinarith