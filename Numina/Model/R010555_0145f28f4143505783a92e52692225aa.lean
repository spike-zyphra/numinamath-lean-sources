import Mathlib

theorem algebra_4111 {k : ℝ} {f g : ℝ → ℝ}
    (hf : ∀ x, f x = 3 * x ^ 2 - 2 * x + 4) (hg : ∀ x, g x = x ^ 2 - k * x - 6)
    (eq : f 10 - g 10 = 10) : k = -18 := by
  have f10 : f 10 = 3 * 10 ^ 2 - 2 * 10 + 4 := hf 10
  have g10 : g 10 = 10 ^ 2 - k * 10 - 6 := hg 10
  rw [f10, g10] at eq
  linarith