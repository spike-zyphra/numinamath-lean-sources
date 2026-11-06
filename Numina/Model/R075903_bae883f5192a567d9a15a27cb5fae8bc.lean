import Mathlib

theorem algebra_232608 {p q : ℝ} (h : p ≠ 0) (h' : q ≠ 0)
    (h1 : (3, 1) ∈ {(x, y) | y = p * x + 4 ∧ p * y = q * x - 7}) :
    q = 2 := by
  rcases h1 with ⟨h_eq1, h_eq2⟩
  have hp : p = -1 := by
    linarith
  rw [hp] at h_eq2
  linarith