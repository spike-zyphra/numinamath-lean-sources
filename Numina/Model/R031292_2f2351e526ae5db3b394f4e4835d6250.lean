import Mathlib

theorem algebra_275988 {a b x y : ℤ} : (a + b) * (x + y) ∣ (a * x + b * y) ^ 3 + (b * x + a * y) ^ 3 := by
  use ( (a * x + b * y)^2 - (a * x + b * y) * (b * x + a * y) + (b * x + a * y)^2 )
  ring