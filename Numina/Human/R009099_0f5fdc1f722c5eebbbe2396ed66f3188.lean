import Mathlib

/- Calculate
\[\prod_{n = 1}^{13} \frac{n(n + 2)}{(n + 4)^2}.\] -/
theorem algebra_14920 : ∏ n ∈ Finset.Icc (1 : ℕ) 13, (n * (n + 2) / (n + 4)^2 : ℚ) = 3 / 161840 := by
  native_decide
