import Mathlib

theorem algebra_14975 {a b : ℝ} (f g : ℝ → ℝ) (hf : ∀ x, f x = a * x + b)
    (hg : ∀ x, g x = 2 * x - 5) (hfg : ∀ x, g (f x) = 3 * x + 4) :
    a + b = 6 := by
  have eq1 := hfg 1
  rw [hf, hg] at eq1
  norm_num at eq1
  linarith