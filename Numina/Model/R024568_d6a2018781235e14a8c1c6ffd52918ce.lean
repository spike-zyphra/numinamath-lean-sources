import Mathlib

theorem algebra_304214 {f : ℝ → ℝ} (hf : ∀ x, x < 0 ∨ x > 0 → f (1 / x) + 1 / x * f (-x) = 4 * x) :
    f 2 * f (-1 / 2) = -31.5 := by

  have eq1 := hf 2 (by right; norm_num)
  have eq2 := hf (-2) (by left; norm_num)
  have eq3 := hf (1 / 2) (by right; norm_num)
  have eq4 := hf (-1 / 2) (by left; norm_num)
  norm_num at eq1 eq2 eq3 eq4
  have h1 : f 2 = 9 := by
    linarith
  have h2 : f (-1 / 2) = -3.5 := by
    linarith
  rw [h1, h2]
  all_goals norm_num