import Mathlib

theorem algebra_234367 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 0 ∧ x ≠ 1 → (x - 1) * f x + f (1 / x) = 1 / (x - 1)) :
    f (2018 / 2019) = 2019 := by
  have eq1 := hf (2018 / 2019) ⟨by norm_num, by norm_num⟩
  have eq2 := hf (2019 / 2018) ⟨by norm_num, by norm_num⟩
  norm_num [show (2018 : ℝ) ≠ 0 by norm_num, show (2019 : ℝ) ≠ 0 by norm_num] at eq1 eq2
  linarith