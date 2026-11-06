import Mathlib

theorem algebra_60214 {a b : ℤ} (p : ℤ → ℤ) (hp : ∀ x, p x = x ^ 2 + a * x + b)
    (n : ℤ) : ∃ M, p n * p (n + 1) = p M := by
  use n ^ 2 + (a + 1) * n + b
  have h1 : p n = n ^ 2 + a * n + b := by 
    specialize hp n
    simpa using hp
  have h2 : p (n + 1) = (n + 1) ^ 2 + a * (n + 1) + b := by
    specialize hp (n + 1)
    simpa using hp
  have h3 : p (n ^ 2 + (a + 1) * n + b) = (n ^ 2 + (a + 1) * n + b) ^ 2 + a * (n ^ 2 + (a + 1) * n + b) + b := by
    specialize hp (n ^ 2 + (a + 1) * n + b)
    simpa using hp
  rw [h1, h2, h3]
  ring