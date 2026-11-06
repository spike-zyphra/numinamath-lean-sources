import Mathlib

theorem algebra_101868 {a b c d : ℤ} (P : ℤ → ℤ)
    (hP : ∀ x, P x = a * x ^ 3 + b * x ^ 2 + c * x + d) (x y : ℤ) (hx : x ≠ y) :
    (x - y) ∣ (P x - P y) := by
  have h1 : P x = a * x ^ 3 + b * x ^ 2 + c * x + d := hP x
  have h2 : P y = a * y ^ 3 + b * y ^ 2 + c * y + d := hP y
  rw [h1, h2]
  use a * (x ^ 2 + x * y + y ^ 2) + b * (x + y) + c
  ring