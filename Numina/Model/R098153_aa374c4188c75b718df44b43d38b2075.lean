import Mathlib

theorem algebra_11632 (f : ℝ → ℝ) (m n : ℝ) (hf : ∀ x, f x = x ^ 2 + m * x + n)
    (h : ¬∃ x ∈ Set.Icc 1 5, |f x| > 2) : f 1 - 2 * f 3 + f 5 = 8 := by
  have h1 : f 1 = 1^2 + m * 1 + n := hf 1
  have h2 : f 3 = 3^2 + m * 3 + n := hf 3
  have h3 : f 5 = 5^2 + m * 5 + n := hf 5
  rw [h1, h2, h3]
  ring