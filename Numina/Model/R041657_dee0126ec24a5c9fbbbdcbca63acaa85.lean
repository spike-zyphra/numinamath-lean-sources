import Mathlib

theorem algebra_291786 {f : ℚ → ℝ} (hf : ∀ x, 0 < f x)
    (h2 : f 2 = 1 / 2) (hinc : ∀ x, f x ≤ 1 → f (x + 1) ≤ 1)
    (hmul : ∀ x y, f (x * y) = f x * f y): false := by

  have h0 : f (0 : ℚ) = 1 := by
    have hmul0 : f ((0 : ℚ) * (0 : ℚ)) = f (0 : ℚ) * f (0 : ℚ) := hmul (0 : ℚ) (0 : ℚ)
    norm_num at hmul0
    have hf0 : 0 < f (0 : ℚ) := hf 0
    nlinarith

  have h4 : f ( (2 : ℚ) * (0 : ℚ) ) = f (2 : ℚ) * f (0 : ℚ) := hmul 2 0
  norm_num at h4
  nlinarith [h0, h2, h4]