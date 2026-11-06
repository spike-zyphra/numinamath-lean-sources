import Mathlib

theorem algebra_304345 (a b c : ℝ) (ha : a ≠ 0) (hA : a * (-1) ^ 2 + b * (-1) + c = 0)
    (hB : a * 2 ^ 2 + b * 2 + c = 0) (hP : ¬∃ x0, a * (x0 + 1) ^ 2 + b * (x0 + 1) + c = 2 * x0 ^ 2 - 2) :
    (x0 + 1, 2 * x0 ^ 2 - 2) = (-1, 6) := by

  have h1 : c = b - a := by linarith

  have h2 : b = -a := by
    rw [show c = b - a by linarith [h1]] at hB 
    linarith

  have h3 : c = -2 * a := by
    linarith [h1, h2]

  have h4 : ∃ x0, a * (x0 + 1) ^ 2 + b * (x0 + 1) + c = 2 * x0 ^ 2 - 2 := by
    use 1 
    simp [h2, h3]
    <;> nlinarith

  contradiction