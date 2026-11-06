import Mathlib

theorem number_theory_258956 {a b p : ℤ} (hp : Prime p) (h1 : ¬p ∣ a) (h2 : ¬p ∣ b)
    (h3 : ∃ x y : ℤ, x^2 - a = p * y) (h4 : ∃ x y : ℤ, x^2 - b = p * y) :
    ∃ x y : ℤ, x^2 - a * b = p * y := by
  rcases h3 with ⟨x1, y1, h3⟩
  rcases h4 with ⟨x2, y2, h4⟩
  use x1 * x2
  use a * y2 + b * y1 + p * (y1 * y2)
  have h5 : x1^2 = a + p * y1 := by linarith
  have h6 : x2^2 = b + p * y2 := by linarith
  calc
    (x1 * x2) ^ 2 - a * b = (x1 ^ 2) * (x2 ^ 2) - a * b := by ring
    _ = (a + p * y1) * (b + p * y2) - a * b := by rw [h5, h6]
    _ = a * b + a * p * y2 + b * p * y1 + p^2 * (y1 * y2) - a * b := by ring
    _ = a * p * y2 + b * p * y1 + p^2 * (y1 * y2) := by ring
    _ = p * (a * y2 + b * y1 + p * (y1 * y2)) := by ring